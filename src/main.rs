#[deny(unused_results)]
use anyhow::{anyhow, Context as _};
use argh::FromArgs;
use i3ipc::reply::{Command, CommandOutcome, Node, NodeLayout, NodeType};
use i3ipc::I3Connection;
use log::{debug, info};

trait NodeExt {
    fn get_focused_child(&self) -> Option<(usize, &Self)>;
}

impl NodeExt for Node {
    fn get_focused_child(&self) -> Option<(usize, &Self)> {
        self.focus.get(0).and_then(|&id| {
            self.nodes
                .iter()
                .enumerate()
                .find(|(_, node)| node.id == id)
        })
    }
}

fn run_command(conn: &mut I3Connection, cmd: &str) -> Result<(), anyhow::Error> {
    info!("running cmd: {}", cmd);
    conn.run_command(cmd)
        .map_err(anyhow::Error::from)
        .and_then(|reply| reply.into_result())
        .context(format!("failed to run command: cmd={}", cmd))?;
    Ok(())
}

trait IntoResult {
    fn into_result(self) -> Result<(), anyhow::Error>;
}

impl IntoResult for Command {
    fn into_result(self) -> Result<(), anyhow::Error> {
        let Command { outcomes } = self;
        outcomes
            .into_iter()
            .map(IntoResult::into_result)
            .collect::<Result<_, _>>()
    }
}

impl IntoResult for CommandOutcome {
    fn into_result(self) -> Result<(), anyhow::Error> {
        let Self { success, error } = self;
        if success {
            Ok(())
        } else {
            if let Some(e) = error {
                Err(anyhow!("command failed with error message: {}", e))
            } else {
                Err(anyhow!("command failed with no error message"))
            }
        }
    }
}

fn find_root_container(mut node: &Node) -> anyhow::Result<&Node> {
    loop {
        if node.nodetype == NodeType::Workspace {
            break;
        } else {
            node = node
                .get_focused_child()
                .ok_or_else(|| anyhow!("node {:?} has no focused child", node))?
                .1;
        }
    }
    loop {
        if node.nodes.len() == 1 && node.nodes[0].percent == Some(1.0) {
            if let Some((_, child)) = node.get_focused_child() {
                node = child;
            } else {
                return Ok(node);
            }
        } else {
            return Ok(node);
        }
    }
}

fn log_tree(indent: &str, node: &Node) {
    let Node {
        name,
        rect,
        percent,
        nodetype,
        focused,
        layout,
        ..
    } = node;
    debug!(
        "{}name={:?}, percent={:?}, rect={:?}, nodetype={:?}, focused={}, layout={:?}",
        indent, name, percent, rect, nodetype, focused, layout
    );
    let indent = indent.to_owned() + "  ";
    for node in node.nodes.iter() {
        log_tree(&indent, node);
    }
}

#[derive(FromArgs)]
/// i3wm helper extensions
struct Args {
    /// log level (defaults to WARN)
    #[argh(option, short = 'l', default = "log::LevelFilter::Warn")]
    log_level: log::LevelFilter,
    #[argh(subcommand)]
    subcommands: SubCommands,
}

#[derive(FromArgs, Debug)]
#[argh(subcommand)]
enum SubCommands {
    LogTree(LogTree),
    Resize(Resize),
    Swap(Swap),
    Rotate(Rotate),
    Push(Push),
    Split(Split),
}

/// LogTree subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "log_tree")]
struct LogTree {}

/// Rotate subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "rotate")]
struct Rotate {
    /// direction to rotate in (either left or right)
    #[argh(positional)]
    direction: Direction,
}

/// Split subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "split")]
struct Split {}

/// Resize subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "resize")]
struct Resize {
    #[argh(positional)]
    percentages: Vec<u64>,
}

/// Swap subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "swap")]
struct Swap {
    /// direction to swap in (either left or right)
    #[argh(positional)]
    direction: Direction,
    /// don't resize both src and dst to maintain their original size
    #[argh(switch, short = 'r')]
    noresize: bool,
}

/// Push subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "push")]
struct Push {
    /// direction to push into (either left or right)
    #[argh(positional)]
    direction: Direction,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Direction {
    Left,
    Right,
}

impl std::str::FromStr for Direction {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "left" => Ok(Self::Left),
            "right" => Ok(Self::Right),
            s => Err(anyhow!("failed to parse as direction: {}", s)),
        }
    }
}

impl std::fmt::Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Left => "left",
                Self::Right => "right",
            }
        )
    }
}

fn is_merged(n: &Node) -> Option<(&Node, &Node)> {
    (n.layout == NodeLayout::Stacked
        && n.nodes
            .iter()
            .all(|Node { layout, .. }| *layout == NodeLayout::Stacked)
        && n.nodes.len() == 2)
        .then(|| (&n.nodes[0], &n.nodes[1]))
}

fn split(conn: &mut I3Connection) -> anyhow::Result<()> {
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    log_tree("", &root);
    let first = root
        .nodes
        .iter()
        .next()
        .ok_or_else(|| anyhow!("no toplevel container"))?;
    let last = root
        .nodes
        .iter()
        .last()
        .ok_or_else(|| anyhow!("no toplevel container"))?;

    // This takes care of the special case of 2 toplevel containers.
    let (middle, side, dir) = if let Some((top, bottom)) = is_merged(root) {
        (top, bottom, Direction::Right)
    } else if let Some((top, bottom)) = is_merged(first) {
        (bottom, top, Direction::Left)
    } else if let Some((top, bottom)) = is_merged(last) {
        (top, bottom, Direction::Right)
    } else {
        return Err(anyhow!("no candidate found"));
    };
    run_command(conn, &format!("[con_id=\"{}\"] move {}", middle.id, dir))?;
    run_command(
        conn,
        &format!("[con_id=\"{}\"] move {1}, move {1}", side.id, dir),
    )?;
    resize(
        conn,
        Resize {
            percentages: vec![],
        },
    )?;
    run_command(conn, "restart")?;
    Ok(())
}

fn push(conn: &mut I3Connection, Push { direction }: Push) -> Result<(), anyhow::Error> {
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    for toplevel in root.nodes.iter() {
        if toplevel.layout != NodeLayout::Stacked {
            run_command(
                conn,
                &format!(
                    "[con_id=\"{}\"] split vertical, layout stacking",
                    toplevel.id
                ),
            )?;
        }
    }

    let root = conn.get_tree()?;
    let (left, right) = focused_and(&root, direction)?;
    if is_merged(left).is_some() || is_merged(right).is_some() {
        return Err(anyhow!("src or dst already merged, not proceeding"));
    }
    run_command(
        conn,
        &format!("[con_id=\"{}\"] split vertical, layout stacking", left.id),
    )?;
    let last_id = left
        .nodes
        .iter()
        .last()
        .ok_or_else(|| anyhow!("right container is empty"))?
        .id;
    run_command(conn, &format!("[con_id=\"{}\"] mark _push", last_id))?;
    run_command(
        conn,
        &format!(
            "[con_id=\"{}\"] move container to mark _push, move down",
            right.id
        ),
    )?;
    resize(
        conn,
        Resize {
            percentages: vec![33],
        },
    )?;

    Ok(())
}

fn resize(
    conn: &mut I3Connection,
    Resize { mut percentages }: Resize,
) -> Result<(), anyhow::Error> {
    let sum = percentages.iter().fold(0, |sum, i| sum + i);
    if sum >= 100 {
        return Err(anyhow!(
            "percentages must sum to less than 100: {:?}",
            percentages
        ));
    }

    let root = conn.get_tree()?;
    let root_container = find_root_container(&root)?;
    log_tree("", root_container);
    if root_container.layout != NodeLayout::SplitH {
        return Err(anyhow!(
            "unexpectedly found top-level container that is not SplitH"
        ));
    }
    let n = root_container.nodes.len();
    match percentages.len() {
        0 => {
            percentages.resize(n - 1, 100 / n as u64);
        }
        1 => {
            if n == 3 {
                percentages.push(if percentages[0] * 2 < 100 {
                    100 - percentages[0] * 2
                } else {
                    (100 - percentages[0]) / 2
                });
            }
        }
        _ => {}
    }
    if n != percentages.len() + 1 {
        return Err(anyhow!(
            "#percentages+1 != #containers; percentages={:?}, #containers={}",
            percentages,
            n
        ));
    }
    let mut delta = 0i64;
    for (con, want) in root_container.nodes[..n - 1].iter().zip(percentages) {
        let percent = con
            .percent
            .ok_or_else(|| anyhow!("missing percentage value in container"))?;
        let percent = (percent * 100.0).round() as u64;
        delta = want as i64 - (percent as i64 + delta);
        let (verb, ppt) = if delta < 0 {
            ("shrink", -delta)
        } else {
            ("grow", delta)
        };
        if ppt > 0 {
            let cmd = format!(
                "[con_id=\"{}\"] resize {} right 1 px or {} ppt",
                con.id, verb, ppt
            );
            run_command(conn, &cmd)?
        }
        delta = -delta;
    }
    Ok(())
}

fn focused_and(root: &Node, direction: Direction) -> anyhow::Result<(&Node, &Node)> {
    let root_container = find_root_container(&root)?;
    log_tree("", root_container);

    let (src_index, src) = root_container
        .get_focused_child()
        .ok_or_else(|| anyhow!("failed to find focused toplevel container"))?;
    Ok(match direction {
        Direction::Left => {
            if src_index == 0 {
                return Err(anyhow!("no container to the left of leftmost container"));
            }
            (&root_container.nodes[src_index - 1], src)
        }
        Direction::Right => {
            if src_index + 1 >= root_container.nodes.len() {
                return Err(anyhow!("no container to the right of rightmost container"));
            }
            (src, &root_container.nodes[src_index + 1])
        }
    })
}

fn swap(
    conn: &mut I3Connection,
    left: &Node,
    right: &Node,
    noresize: bool,
) -> Result<(), anyhow::Error> {
    if !noresize {
        let right_percent = right
            .percent
            .ok_or_else(|| anyhow!("failed to find right container percent"))?;
        let left_percent = left
            .percent
            .ok_or_else(|| anyhow!("failed to find left container percent"))?;
        let delta = ((right_percent - left_percent) * 100.0) as i64;
        let (verb, ppt) = if delta < 0 {
            ("shrink", -delta)
        } else {
            ("grow", delta)
        };
        let cmd = format!(
            "[con_id=\"{}\"] resize {} right 1 px or {} ppt",
            left.id, verb, ppt
        );
        run_command(conn, &cmd)?;
    }

    let cmd = format!(
        "[con_id=\"{}\"] swap container with con_id {}",
        left.id, right.id
    );
    run_command(conn, &cmd)?;
    Ok(())
}

fn rotate(conn: &mut I3Connection, Rotate { direction }: Rotate) -> anyhow::Result<()> {
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    match direction {
        Direction::Left => {
            let mut iter = root.nodes.iter();
            let first = match iter.next() {
                Some(node) => node,
                None => return Ok(()),
            };
            for node in iter {
                swap(conn, first, node, false)?;
            }
        }
        Direction::Right => {
            let mut iter = root.nodes.iter().rev();
            let last = match iter.next() {
                Some(node) => node,
                None => return Ok(()),
            };
            for node in iter {
                swap(conn, node, last, false)?;
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), anyhow::Error> {
    let Args {
        log_level,
        subcommands,
    } = argh::from_env();
    let () = simple_logger::SimpleLogger::new()
        .with_level(log_level)
        .init()
        .context("failed to initialize simple logger")?;
    let mut conn = I3Connection::connect()?;
    let () = match subcommands {
        SubCommands::LogTree(LogTree {}) => {
            let root = conn.get_tree()?;
            let root = find_root_container(&root)?;
            log_tree("", &root);
        }
        SubCommands::Resize(args) => resize(&mut conn, args)?,
        SubCommands::Swap(Swap {
            direction,
            noresize,
        }) => {
            let root = conn.get_tree()?;

            let (left, right) = focused_and(&root, direction)?;
            swap(&mut conn, left, right, noresize)?;
        }
        SubCommands::Push(args) => push(&mut conn, args)?,
        SubCommands::Split(Split {}) => split(&mut conn)?,
        SubCommands::Rotate(args) => rotate(&mut conn, args)?,
    };
    Ok(())
}
