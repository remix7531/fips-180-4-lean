-- Wrap code blocks preceded by a `<!-- eqn:N.M -->` HTML comment in a flex
-- container with the equation tag right-aligned beside the code. Styling
-- lives in `style.html` under `.eqn-row` / `.eqn-tag`.

function Blocks(blocks)
  local out = pandoc.List()
  local i = 1
  while i <= #blocks do
    local b = blocks[i]
    local tag = nil
    if b.t == "RawBlock" and b.format:match("^html") then
      tag = b.text:match("<!%-%-%s*eqn:%s*([%w%.]+)%s*%-%->")
    end
    if tag and blocks[i + 1] and blocks[i + 1].t == "CodeBlock" then
      out:insert(pandoc.RawBlock("html",
        '<div class="eqn-row"><div class="eqn-flex"><div class="eqn-code">'))
      out:insert(blocks[i + 1])
      out:insert(pandoc.RawBlock("html",
        '</div><div class="eqn-tag">(' .. tag .. ')</div></div></div>'))
      i = i + 2
    else
      out:insert(b)
      i = i + 1
    end
  end
  return out
end
