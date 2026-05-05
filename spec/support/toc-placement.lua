-- Replaces a fenced div `::: toc\n:::` with a nested table of contents
-- built from the document's headers (up to level 3).

local max_level = 3

local function collect_headers(blocks)
  local out = {}
  for _, b in ipairs(blocks) do
    if b.t == 'Header' and b.level <= max_level
       and not b.classes:includes('unnumbered') then
      table.insert(out, b)
    end
  end
  return out
end

local function build_toc(headers)
  local i = 1
  local function build(min_level)
    local items = pandoc.List()
    while i <= #headers do
      local h = headers[i]
      if h.level < min_level then break end
      if h.level == min_level then
        local link = pandoc.Link(h.content, '#' .. h.identifier)
        local item = pandoc.List({ pandoc.Plain({ link }) })
        i = i + 1
        if i <= #headers and headers[i].level > min_level then
          local sub = build(min_level + 1)
          if #sub.content > 0 then
            item:insert(sub)
          end
        end
        items:insert(item)
      else
        i = i + 1
      end
    end
    return pandoc.BulletList(items)
  end
  local min_level = headers[1].level
  for _, h in ipairs(headers) do
    if h.level < min_level then min_level = h.level end
  end
  return build(min_level)
end

function Pandoc(doc)
  local headers = collect_headers(doc.blocks)
  if #headers == 0 then return doc end

  local toc_list = build_toc(headers)
  local toc_nav = pandoc.Div({ toc_list }, pandoc.Attr('TOC'))

  local new_blocks = pandoc.List()
  for _, block in ipairs(doc.blocks) do
    if block.t == 'Div' and block.classes:includes('toc') then
      new_blocks:insert(toc_nav)
    else
      new_blocks:insert(block)
    end
  end
  doc.blocks = new_blocks
  return doc
end
