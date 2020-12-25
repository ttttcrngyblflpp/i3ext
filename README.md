# i3ext (i3wm extensions)

`i3ext` is a rust binary which extends i3wm's functionality by building on top of the IPC commands
made available. It attempts to solve a few ergonomic issues with i3 that are exacerbated when using
it with an ultrawide monitor.

These extensions make the assumption that workspaces are in SplitH layout (note that i3wm's split
directions are flipped around versus the rest of the world, in any case a SplitH is a series of
containers arranged horizontally from left-to-right), and a container in this SplitH is referred to
from here on as a *top-level container*. Due to the width of an ultrawide monitor and the tiling
requirement of i3wm, generally it makes sense to have 3 top-level containers. Even when there are
only 2 windows that need to be simultaneously visible, it is still useful to have a *placeholder
container* so that the other two containers can be positioned on the screen as best as possible.
As a general rule, the left side of a window is more important than the right side of a window as
English reads left-to-right, so it generally makes sense for the leftmost container to be the
placeholder as the left edge of the display is less comfortable to look at than the left portion of
the rightmost container.

## Resize subcommand

The resize subcommand can be used to resize all top-level containers to take up a certain percentage
of the width of their parent (which happens to equal the width of the workspace/output/physical
display). This is a somewhat obvious improvements to the facilities provided by i3wm itself for
resizing containers: the `resize` command is finicky and requires too many keybinds, and
right-click-and-dragging requires using the mouse. Note that resizing is a requirement somewhat
unique to ultrawide users: on 16:9 displays, applications will naturally want to either take up 100%
of the width if they're width hungry, or they're happy taking up 50%, and pretty much no application
will look okay at 33%. On 10:16 displays (a 16:10 display in portrait mode, the widest reasonable
portrait mode aspect ratio), pretty much all applications will want to use up the entire width of
the display. This means that there is usually no point in resizing because the default splits work
"okay", and even when one wants to it boils down to taking away width from one window to give to
another. Ultrawide displays are essentially multiple portrait-mode displays side-by-side, except the
displays' widths can be adjusted, and such adjustments come down to resizing toplevel
containers such that all windows are assigned their natural size and positioned in the most
comfortable spots possible.

For the examples below, it is assumed that there are three top-level containers. Note that the
percentage values passed to the resize subcommand are in order from left-to-right, and normally do
not sum to 100 but it is implied that any remaining space is given to the rightmost container.

### Examples

Resize the three containers to have equal widths.

```
i3ext resize 33 33
```

Resize the leftmost container to take up 25% of the total width as a placeholder window, the middle
container to take up 33% of the total width (which is about right for a text editor) and the
rightmost container to take up the rest of the space (42%, about right for a web browser).

```
i3ext resize 25 33
```

Resize the leftmost and rightmost placeholder containers to take up 20% of total width, leaving the
middle container 60% of total width to display any width-hungry applications.

```
i3ext resize 20 60
```

The resize subcommand works well in conjunction with `i3-input`, which can be used to take input
from the user for what the percentage values to use.

## Swap subcommand

The swap subcommand can be used to swap adjacent top-level containers. It takes a direction, either
left or right, and swaps the currently-focused container with the container in that direction.

Note that this behavior is exactly the same as the move command if both top-level containers
involved in the swap are windows. When the top-level containers are proper containers, swapping them
requires the i3wm "swap" command. This subcommand addresses the ergonomics issues of the swap
command not having a direction, and the usually non-desirable property that the sizes of the
containers are swapped as well. Note also that the swap subcommand does not cross display
boundaries, i.e. it does not support swapping two containers that are on different displays.

## TODO

- [x] Make swap preserve widths by default, and add a flag to not preserve width.
- [ ] Add a rotate subcommand which rotates all toplevel containers to the left or right.
- [ ] Make swap be able to swap the leftmost container with the rightmost container.
