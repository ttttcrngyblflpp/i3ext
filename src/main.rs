use anyhow::{anyhow, Context as _};
use argh::FromArgs;
use i3ipc::reply::{Command, CommandOutcome, Node, NodeLayout, NodeType};
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

trait CommandExt {
    fn into_result(self) -> Result<(), anyhow::Error>;
}

impl CommandExt for Command {
    fn into_result(self) -> Result<(), anyhow::Error> {
        let Command { outcomes } = self;
        outcomes.into_iter().map(CommandOutcomeExt::into_result).collect::<Result<_, _>>()
    }
}

trait CommandOutcomeExt {
    fn into_result(self) -> Result<(), anyhow::Error>;
}

impl CommandOutcomeExt for CommandOutcome {
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

fn find_root_container(mut node: &Node) -> Option<&Node> {
    loop {
        if node.nodetype == NodeType::Workspace {
            break;
        } else {
            node = node.get_focused_child()?.1;
        }
    }
    loop {
        if node.nodes.len() == 1 && node.nodes[0].percent == Some(1.0) {
            if let Some((_, child)) = node.get_focused_child() {
                node = child;
            } else {
                return Some(node);
            }
        } else {
            return Some(node);
        }
    }
}

fn log_tree(indent: &str, node: &Node) {
    let Node {
        name,
        percent,
        nodetype,
        focused,
        layout,
        ..
    } = node;
    debug!(
        "{}name={:?}, percent={:?}, nodetype={:?}, focused={}, layout={:?}",
        indent, name, percent, nodetype, focused, layout
    );
    let indent = indent.to_owned() + "  ";
    for node in node.nodes.iter() {
        log_tree(&indent, node);
    }
}

#[derive(FromArgs)]
/// i3wm helper extensions
struct Args {
    #[argh(subcommand)]
    subcommands: SubCommands,
}

#[derive(FromArgs, Debug)]
#[argh(subcommand)]
enum SubCommands {
    Resize(Resize),
    Swap(Swap),
}

/// Resize subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "resize")]
struct Resize {
    /// dry-run (don't actually run any commands)
    #[argh(switch, short = 'd')]
    dry_run: bool,
    #[argh(positional)]
    percentages: Vec<u64>,
}

/// Swap subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "swap")]
struct Swap {
    /// dry-run (don't actually run any commands)
    #[argh(switch, short = 'd')]
    dry_run: bool,
    #[argh(positional)]
    direction: Direction,
}

#[derive(Debug, PartialEq, Eq)]
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

fn resize(args: Resize) -> Result<(), anyhow::Error> {
    let Resize {
        dry_run,
        mut percentages,
    } = args;
    let sum = percentages.iter().fold(0, |sum, i| sum + i);
    if sum > 100 {
        return Err(anyhow!(
            "percentages cannot sum to over 100: {:?}",
            percentages
        ));
    } else if sum == 100 {
        percentages.pop();
    }

    let mut conn = i3ipc::I3Connection::connect()?;
    let root = conn.get_tree()?;
    let root_container =
        find_root_container(&root).ok_or_else(|| anyhow!("failed to find root container"))?;
    log_tree("", root_container);
    if root_container.layout != NodeLayout::SplitH {
        return Err(anyhow!(
            "unexpectedly found top-level container that is not SplitH"
        ));
    }
    let n = root_container.nodes.len();
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
            info!("running cmd: {}", cmd);
            if !dry_run {
                let () = conn.run_command(&cmd)
                    .map_err(anyhow::Error::from)
                    .and_then(|reply| reply.into_result())
                    .context(format!("failed to run command: cmd={}", cmd))?;
            }
        }
        delta = -delta;
    }
    Ok(())
}

fn swap(args: Swap) -> Result<(), anyhow::Error> {
    let Swap { dry_run, direction } = args;
    let mut conn = i3ipc::I3Connection::connect()?;
    let root = conn.get_tree()?;
    let root_container =
        find_root_container(&root).ok_or_else(|| anyhow!("failed to find root container"))?;
    log_tree("", root_container);

    let (src_index, src) = root_container
        .get_focused_child()
        .ok_or_else(|| anyhow!("failed to find focused toplevel container"))?;
    let dst = match direction {
        Direction::Left => {
            if src_index == 0 {
                return Err(anyhow!("no container to the left of leftmost container"));
            }
            &root_container.nodes[src_index - 1]
        }
        Direction::Right => {
            if src_index + 1 >= root_container.nodes.len() {
                return Err(anyhow!("no container to the right of rightmost container"));
            }
            &root_container.nodes[src_index + 1]
        }
    };

    let cmd = format!("[con_id=\"{}\"] swap container with con_id {}", src.id, dst.id);
    info!("running cmd: {}", cmd);
    if !dry_run {
        let () = conn.run_command(&cmd)
            .map_err(anyhow::Error::from)
            .and_then(|reply| reply.into_result())
            .context(format!("failed to run command: cmd={}", cmd))?;
    }
    Ok(())
}

fn main() -> Result<(), anyhow::Error> {
    let () = simple_logger::SimpleLogger::new()
        .init()
        .context("failed to initialize simple logger")?;
    let Args { subcommands } = argh::from_env();
    let () = match subcommands {
        SubCommands::Resize(args) => resize(args)?,
        SubCommands::Swap(args) => swap(args)?,
    };
    Ok(())
}
