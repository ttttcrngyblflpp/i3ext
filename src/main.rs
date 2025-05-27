#[deny(unused_results)]
use anyhow::{anyhow, bail, Context as _};
use argh::FromArgs;
use i3ipc::reply::{Command, CommandOutcome, Node, NodeLayout, NodeType, WindowProperty};
use i3ipc::I3Connection;
use log::{debug, info};

trait NodeExt {
    fn get_focused_child(&self) -> Option<(usize, &Self)>;
    fn kind(&self) -> WindowKind;
    fn percentages_cumulative(&self) -> Vec<f64>;
    fn percentages(&self) -> Vec<f64>;
    fn widths(&self) -> Vec<i32>;
    fn right_x(&self) -> Vec<i32>;
    fn resize_stats(&self) -> ResizeStats;
    fn left_right(&self, i: usize) -> (Vec<ResizeStats>, Vec<ResizeStats>);
    fn desired(&self) -> f64;
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

    fn kind(&self) -> WindowKind {
        if let Some(properties) = self.window_properties.as_ref() {
            let Some(class) = properties.get(&WindowProperty::Class) else {
                return WindowKind::Browser;
            };
            if class == "Alacritty" {
                return WindowKind::Terminal;
            }
            return WindowKind::Browser;
        }
        if self
            .nodes
            .iter()
            .all(|node| node.kind() == WindowKind::Terminal)
        {
            return WindowKind::Terminal;
        }
        return WindowKind::Browser;
    }

    fn resize_stats(&self) -> ResizeStats {
        ResizeStats {
            percentage: self.percent.expect("missing percentage"),
            kind: self.kind(),
        }
    }

    fn left_right(&self, i: usize) -> (Vec<ResizeStats>, Vec<ResizeStats>) {
        let left_windows = self.nodes[..i]
            .iter()
            .map(NodeExt::resize_stats)
            .collect::<Vec<_>>();
        let right_windows = self.nodes[i + 1..]
            .iter()
            .rev()
            .map(NodeExt::resize_stats)
            .collect::<Vec<_>>();
        (left_windows, right_windows)
    }

    fn percentages_cumulative(&self) -> Vec<f64> {
        cumulative_sum(self.nodes.iter().map(|node| node.percent.unwrap())).collect::<Vec<_>>()
    }

    fn percentages(&self) -> Vec<f64> {
        self.nodes
            .iter()
            .map(|con| con.percent.expect("missing percentage"))
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

    fn desired(&self) -> f64 {
        Config::default()
            .desired(self.kind())
            .max(self.percent.expect("missing percent"))
    }
}

fn cumulative_sum(iter: impl IntoIterator<Item = f64>) -> impl Iterator<Item = f64> {
    let mut acc = 0f64;
    iter.into_iter().map(move |v| {
        acc += v;
        acc
    })
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
        window_properties,
        nodetype,
        focused,
        layout,
        ..
    } = node;
    debug!(
        "{}name={:?}, percent={:?}, window_properties={:?}, rect={:?}, nodetype={:?}, focused={}, layout={:?}",
        indent,
        name,
        percent,
        window_properties,
        rect,
        nodetype,
        focused,
        layout
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
    ResizeAll(ResizeAll),
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
    /// direction of the percentages provided
    #[argh(option)]
    direction: Option<Direction>,
    /// the new percentage of the window (uses per-window-kind default if not provided)
    #[argh(option)]
    percentage: Option<f64>,
}

/// ResizeAll subcommand.
#[derive(FromArgs, Debug)]
#[argh(subcommand, name = "resize-all")]
struct ResizeAll {
    /// direction of the percentages provided
    #[argh(option, default = "Direction::Right")]
    direction: Direction,
    #[argh(positional)]
    percentages: Vec<f64>,
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

fn resize_all(
    conn: &mut I3Connection,
    // Left means left-to-right.
    dir: Direction,
    mut dst_percentages: Vec<f64>,
) -> Result<(), anyhow::Error> {
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

    // i3 can report percentages that sum to slightly more than 1, so
    // we need to renormalize here.
    let mut sum: f64 = dst_percentages.iter().sum();
    if sum > 1.01 {
        bail!("percentages must sum to <= 1.01: {sum} {:?}", dst_percentages);
    }
    if sum > 1. {
        for i in dst_percentages.iter_mut() {
            *i = *i / sum;
        }
        sum = 1.;
    }

    if dst_percentages.len() > n {
        bail!("too many percentages passed: {:?}", dst_percentages);
    } else if dst_percentages.len() < n {
        let omitted_count = n - dst_percentages.len();
        for _ in 0..omitted_count {
            dst_percentages.push((1.0 - sum) / omitted_count as f64);
        }
    }
    if dir == Direction::Right {
        dst_percentages.reverse();
    }

    let mut dst_pixels = dst_percentages
        .into_iter()
        .map(|i| {
            // Don't use trunc here, it just makes things worse!
            let i = (i * total_width as f64) as i32;
            if i == 0 {
                1
            } else {
                i
            }
        })
        .collect::<Vec<i32>>();
    let mut extra = dst_pixels.iter().copied().sum::<i32>() - total_width;
    if extra > 0 {
        for i in dst_pixels.iter_mut() {
            if *i == 1 {
                continue;
            }
            let take = std::cmp::min(*i - 1, extra);
            *i -= take;
            extra -= take;
            if extra == 0 {
                break;
            }
        }
    }
    // dst needs to have in pixels, where the right edge of each column should
    // be (except for the rightmost column).
    let dst = {
        let mut acc = 0;
        let mut dst = dst_pixels
            .into_iter()
            .map(|x| {
                acc += x;
                acc
            })
            .collect::<Vec<_>>();
        dst.pop();
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

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum WindowKind {
    Terminal,
    Browser,
}

struct ResizeStats {
    percentage: f64,
    kind: WindowKind,
}

// The windows are assumed to always be listed from left-to-right. On the right
// side the slice should be reversed before being passed in.
//
// Returns the new percentages and the actual amount adjusted.
//
// Precondition: if delta > 0, the growing must be possible
fn adjust(windows: &mut [ResizeStats], config: Config, delta: f64) -> (Vec<f64>, f64) {
    if delta > 0. {
        (grow(windows, config, delta), delta)
    } else if delta < 0. {
        let (widths, adjusted) = shrink(windows, -delta);
        (widths, -adjusted)
    } else {
        panic!("no point making a zero adjustment");
    }
}

fn grow(windows: &mut [ResizeStats], config: Config, mut delta: f64) -> Vec<f64> {
    // Go right to left and increase up to desired percentage. If there is leftover,
    // give it all to the leftmost window.
    for window in windows.iter_mut().rev() {
        if window.percentage < config.desired(window.kind) {
            let can_grow = delta.min(config.desired(window.kind) - window.percentage);
            window.percentage += can_grow;
            delta -= can_grow;
            if delta == 0. {
                break;
            }
        }
    }
    if delta > 0. {
        windows[0].percentage += delta;
    }
    windows.iter().map(|stats| stats.percentage).collect()
}

// `delta` is allowed to be larger than the combined percentage of `windows`.
//
// `delta` must be positive, and the returned value is also positive.
fn shrink(windows: &mut [ResizeStats], mut delta: f64) -> (Vec<f64>, f64) {
    let mut adjusted = 0.;
    // Take from left to right.
    if delta > 0. {
        for window in windows.iter_mut() {
            let can_shrink = window.percentage.min(delta);
            window.percentage -= can_shrink;
            adjusted += can_shrink;
            delta -= can_shrink;
            if delta == 0. {
                break;
            }
        }
    }
    (
        windows.iter().map(|stats| stats.percentage).collect(),
        adjusted,
    )
}

fn resize(
    conn: &mut I3Connection,
    config: Config,
    dir: Option<Direction>,
    percentage: Option<f64>,
) -> Result<(), anyhow::Error> {
    if percentage == Some(0.) {
        return Ok(());
    }
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    let (i, _) = root
        .get_focused_child()
        .ok_or_else(|| anyhow!("no top-level container apparently"))?;
    let focused = &root.nodes[i];
    let focused_percent = focused.percent.expect("percent missing");
    let (mut left_windows, mut right_windows) = root.left_right(i);
    let mut delta = percentage.unwrap_or_else(|| config.desired(focused.kind()) - focused_percent);

    if delta < 0. && -delta > focused_percent {
        delta = -focused_percent;
    }

    let percentages = match dir {
        None => {
            if i == 0 || i == root.nodes.len() - 1 {
                bail!("cannot resize centered on left or rightmost container");
            }
            let (left_percentages, l) = adjust(left_windows.as_mut_slice(), config, -delta / 2.);
            let (right_percentages, r) = adjust(right_windows.as_mut_slice(), config, -delta / 2.);
            left_percentages
                .into_iter()
                .chain(std::iter::once(focused_percent - l - r))
                .chain(right_percentages.into_iter().rev())
                .collect::<Vec<_>>()
        }
        Some(Direction::Left) => {
            if i == 0 {
                bail!("cannot resize left on leftmost container");
            }
            let (left_percentages, adjustment) =
                adjust(left_windows.as_mut_slice(), config, -delta);
            left_percentages
                .into_iter()
                .chain(std::iter::once(focused_percent - adjustment))
                .chain(
                    root.nodes[i + 1..]
                        .iter()
                        .map(|node| node.percent.expect("percent missing")),
                )
                .collect()
        }
        Some(Direction::Right) => {
            if i == root.nodes.len() - 1 {
                bail!("cannot resize right on rightmost container");
            }
            let (right_percentages, adjustment) =
                adjust(right_windows.as_mut_slice(), config, -delta);
            root.nodes[..i]
                .iter()
                .map(|node| node.percent.expect("percent missing"))
                .chain(std::iter::once(focused_percent - adjustment))
                .chain(right_percentages.into_iter().rev())
                .collect()
        }
    };

    resize_all(conn, Direction::Left, percentages)
}

fn center(
    conn: &mut I3Connection,
    config: Config,
    dir: Option<Direction>,
) -> Result<(), anyhow::Error> {
    let root = conn.get_tree()?;
    let root = find_root_container(&root)?;
    let (i, _) = root
        .get_focused_child()
        .ok_or_else(|| anyhow!("no top-level container apparently"))?;
    let current = root.nodes[i].percent.expect("percent missing");
    let desired = root.nodes[i].desired();
    let delta = if desired > current {
        desired - current
    } else {
        0f64
    };
    let percentages_cumulative = {
        let mut percentages = root.percentages();
        percentages[i] = desired;
        cumulative_sum(percentages.into_iter()).collect::<Vec<_>>()
    };
    // Figure out if we need to move left or right.
    let con_center = match dir {
        None => {
            if i == 0 {
                anyhow::bail!("cannot center leftmost top-level container");
            }
            if i == root.nodes.len() - 1 {
                anyhow::bail!("cannot center rightmost top-level container");
            }
            (percentages_cumulative[i] + percentages_cumulative[i - 1]) / 2.0
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
    let (mut left_windows, mut right_windows) = root.left_right(i);
    let center = root.percentages().iter().sum::<f64>() / 2.0;
    let (left, right) = if (con_center * 100.0).round() == (center * 100.0).round() {
        (
            left_windows
                .iter()
                .map(|rs| rs.percentage)
                .collect::<Vec<_>>(),
            right_windows
                .iter()
                .map(|rs| rs.percentage)
                .collect::<Vec<_>>(),
        )
    } else if con_center > center {
        // Shrink left and grow right.
        let from_center = con_center - center;
        let (left, shrunk) = shrink(left_windows.as_mut_slice(), from_center + delta);
        let right = grow(right_windows.as_mut_slice(), config, shrunk - delta);
        (left, right)
    } else {
        // Shrink right and grow left.
        let from_center = center - con_center;
        let (right, shrunk) = shrink(right_windows.as_mut_slice(), from_center + delta);
        let left = grow(left_windows.as_mut_slice(), config, shrunk - delta);
        (left, right)
    };
    let mut percentages: Vec<_> = left
        .into_iter()
        .chain(std::iter::once(desired))
        .chain(right.into_iter().rev())
        .collect();
    debug!("performing resize: {:?}", percentages);

    // NB: Pop the last percentage and let resize figure it out because i3
    // reports sum of percentages to be >1.
    percentages.pop();

    // Perform the resize.
    resize_all(conn, Direction::Left, percentages)
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

#[derive(Clone, Copy, PartialEq)]
struct Config {
    terminal: f64,
    browser: f64,
}

impl std::default::Default for Config {
    fn default() -> Self {
        Self {
            terminal: 0.16,
            browser: 0.25,
        }
    }
}

impl Config {
    fn desired(&self, kind: WindowKind) -> f64 {
        match kind {
            WindowKind::Terminal => self.terminal,
            WindowKind::Browser => self.browser,
        }
    }
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
    let config = Config::default();
    let mut conn = I3Connection::connect()?;
    let () = match subcommands {
        SubCommands::LogTree(LogTree {}) => {
            let root = conn.get_tree()?;
            let root = find_root_container(&root)?;
            log_tree("", &root);
        }
        SubCommands::Resize(Resize {
            direction,
            percentage,
        }) => {
            debug!("resize percentage: {percentage:?}");
            let percentage = percentage.map(|i| i / 100f64);
            resize(&mut conn, config, direction, percentage)?
        }
        SubCommands::ResizeAll(ResizeAll {
            direction,
            mut percentages,
        }) => {
            for f in percentages.iter_mut() {
                *f /= 100f64;
            }
            resize_all(&mut conn, direction, percentages)?
        }
        SubCommands::Swap(Swap {
            direction,
            noresize,
        }) => {
            let root = conn.get_tree()?;

            let (left, right) = focused_and(&root, direction)?;
            swap(&mut conn, left, right, noresize)?;
        }
        SubCommands::Rotate(args) => rotate(&mut conn, args)?,
        SubCommands::Center(Center { direction }) => center(&mut conn, config, direction)?,
    };
    Ok(())
}
