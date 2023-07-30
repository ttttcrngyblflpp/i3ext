#[deny(unused_results)]
use anyhow::{anyhow, bail, Context as _};
use argh::FromArgs;
use i3ipc::reply::{Command, CommandOutcome, Node, NodeLayout, NodeType};
use i3ipc::I3Connection;
use log::{debug, info};

trait NodeExt {
    fn get_focused_child(&self) -> Option<(usize, &Self)>;
    fn percentages_cumulative(&self) -> Vec<u64>;
    fn percentages(&self) -> Vec<u64>;
    fn widths(&self) -> Vec<i32>;
    fn right_x(&self) -> Vec<i32>;
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

    fn percentages_cumulative(&self) -> Vec<u64> {
        let mut acc = 0;
        self.nodes
            .iter()
            .take(self.nodes.len() - 1)
            .map(|con| {
                acc += (con.percent.expect("missing percentage value in container") * 100.0).round()
                    as u64;
                acc
            })
            .collect::<Vec<_>>()
    }

    fn percentages(&self) -> Vec<u64> {
        self.nodes
            .iter()
            .map(|con| (con.percent.expect("missing percentage") * 100.0).round() as u64)
            .collect::<Vec<_>>()
    }

    fn widths(&self) -> Vec<i32> {
        self.nodes.iter().map(|con| con.rect.2).collect::<Vec<_>>()
    }

    fn right_x(&self) -> Vec<i32> {
        let mut acc = 0;
        self.nodes
            .iter()
            .take(self.nodes.len() - 1)
            .map(|con| {
                acc += con.rect.2;
                acc
            })
            .collect::<Vec<_>>()
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
    Center(Center),
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

/// Center subcommand.
///
/// Does nothing if the focused column is an outer column, or if there is not
/// enough space to steal from the outer columns to perform the operation.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "center")]
struct Center {
    /// direction to center in (either left or right)
    #[argh(positional)]
    direction: Option<Direction>,
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

fn resize(conn: &mut I3Connection, dst_percentages: Vec<u64>) -> Result<(), anyhow::Error> {
    let root = conn.get_tree()?;
    let root_container = find_root_container(&root)?;
    log_tree("", root_container);
    if root_container.layout != NodeLayout::SplitH {
        return Err(anyhow!(
            "unexpectedly found top-level container that is not SplitH"
        ));
    }
    let n = root_container.nodes.len();
    let total_width: i32 = root_container.widths().into_iter().sum();

    if dst_percentages.len() >= n {
        bail!("too many percentages passed: {:?}", dst_percentages);
    }
    let dst = {
        let mut sum_percent = 0;
        let mut dst = Vec::new();
        for (i, percent) in dst_percentages.iter().copied().enumerate() {
            sum_percent += percent;
            if sum_percent >= 100 {
                bail!("percentages must sum to <= 100: {:?}", dst_percentages);
            }

            dst.push(
                if i > 0 { dst[i - 1] } else { 0 }
                    + (total_width as f64 * percent as f64 / 100.0) as i32,
            );
        }

        if (n - 1) > dst_percentages.len() {
            let delta = n - dst_percentages.len();
            let omitted_percent = (100.0 - sum_percent as f64) / (delta as f64);
            for i in dst_percentages.len()..(n - 1) {
                dst.push(
                    if i > 0 { dst[i - 1] } else { 0 }
                        + (total_width as f64 * omitted_percent as f64 / 100.0) as i32,
                );
            }
        }
        dst
    };

    let mut src = root_container.right_x();

    // Proof of why it's always possible to align at least one edge per iteration
    // of the loop: the only way container[0]'s right edge cannot be aligned is
    // if it extends past container[1]'s current right edge. The only way container[1]'s
    // right edge cannot be aligned is if it extends past container[2]'s currenty right
    // edge. This cannot repeat indefinitely, at maximum the rightmost container
    // can be shrunk so that its left edge is in the correct place.
    loop {
        let mut count = 0;
        for i in 0..=n - 2 {
            if src[i] == dst[i] {
                count += 1;
            } else if (i == n - 2 && src[i] < dst[i])
                || (i < n - 2 && src[i] < dst[i] && dst[i] < src[i + 1])
            {
                let cmd = format!(
                    "[con_id=\"{}\"] resize grow right {} px",
                    root_container.nodes[i].id,
                    dst[i] - src[i],
                );
                run_command(conn, &cmd).context(format!("resizing index {}", i))?;
                src[i] = dst[i];
                count += 1;
            } else if (i == 0 && dst[i] < src[i])
                || (i > 0 && src[i - 1] < dst[i] && dst[i] < src[i])
            {
                let cmd = format!(
                    "[con_id=\"{}\"] resize shrink right {} px",
                    root_container.nodes[i].id,
                    src[i] - dst[i],
                );
                run_command(conn, &cmd).context(format!("resizing index {}", i))?;
                src[i] = dst[i];
                count += 1;
            }
        }
        if count == n - 1 {
            break;
        }
    }
    Ok(())
}

fn center(conn: &mut I3Connection, dir: Option<Direction>) -> Result<(), anyhow::Error> {
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    let (i, _) = root
        .get_focused_child()
        .ok_or_else(|| anyhow!("no top-level container apparently"))?;
    // Figure out if we need to move left or right.
    let percentages_cumulative = root.percentages_cumulative();
    let mut percentages = root.percentages();
    let con_center = match dir {
        None => {
            if i == 0 {
                anyhow::bail!("cannot center leftmost top-level container");
            }
            if i == root.nodes.len() - 1 {
                anyhow::bail!("cannot center rightmost top-level container");
            }
            (percentages_cumulative[i] + percentages_cumulative[i - 1]) / 2
        }
        Some(Direction::Left) => {
            if i == 0 {
                anyhow::bail!("cannot center left side of leftmost top-level container");
            }
            percentages_cumulative[i - 1]
        }
        Some(Direction::Right) => {
            if i == root.nodes.len() - 1 {
                anyhow::bail!("cannot center right side of rightmost top-level container");
            }
            percentages_cumulative[i]
        }
    };
    if con_center == 50 {
        return Ok(());
    } else if con_center > 50 {
        let from_center = con_center - 50;
        percentages[0] = if percentages[0] > from_center {
            percentages[0] - from_center
        } else {
            1
        };
    } else {
        let from_center = 50 - con_center;
        let last = *percentages.last().unwrap();
        percentages[0] += if last > from_center {
            from_center
        } else {
            last - 1
        };
    }
    let _ = percentages.pop();

    debug!("performing resize: {:?}", percentages);

    // Perform the resize.
    resize(conn, percentages)
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
        let right_width = right.rect.2;
        let left_width = left.rect.2;
        let delta = right_width - left_width;
        if delta != 0 {
            let (verb, delta) = if delta < 0 {
                ("shrink", -delta)
            } else {
                ("grow", delta)
            };
            let cmd = format!(
                "[con_id=\"{}\"] resize {} right {} px",
                left.id, verb, delta
            );
            run_command(conn, &cmd)?;
        }
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
        SubCommands::Resize(Resize { percentages }) => resize(&mut conn, percentages)?,
        SubCommands::Swap(Swap {
            direction,
            noresize,
        }) => {
            let root = conn.get_tree()?;

            let (left, right) = focused_and(&root, direction)?;
            swap(&mut conn, left, right, noresize)?;
        }
        SubCommands::Rotate(args) => rotate(&mut conn, args)?,
        SubCommands::Center(Center { direction }) => center(&mut conn, direction)?,
    };
    Ok(())
}
