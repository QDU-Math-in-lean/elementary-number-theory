#!/usr/bin/env python3
"""Convert .lean files in `input/` to JSON files in `output/`.

Rules:
- One .lean -> one .json (same base name).
- For each occurrence of the marker `--666`, take the following segment
  (until next `--666` or EOF) and split into three parts:
  1) a block comment like `/- ... -/` (the file uses `/-- ... -/` too)
  2) the part starting with the keyword `theorem` (if present)
  3) the remaining text (topic)
- Each part is collapsed to a single-line string and whitespace/special
  characters are escaped (` ` -> `\s`, `\n` -> `\\n`, `\t` -> `\\t`, etc.).
"""

import os
import re
import json
from glob import glob


def escape_text(s: str) -> str:
	# Escape backslash first
	s = s.replace('\\', '\\\\')
	s = s.replace('\r', '\\r')
	s = s.replace('\n', '\\n')
	s = s.replace('\t', '\\t')
	s = s.replace('"', '\\"')
	# Explicitly escape space to the token \s as requested
	s = s.replace(' ', '\\s')
	return s


def split_segment(segment: str):
	"""Extract the block comment, determine the first word after the comment
	(returned as `type_word`) and the rest of the following text as `output`.

	All returned strings are single-line with whitespace collapsed and
	escaped using `escape_text`.
	"""
	# Find first block comment like /- ... -/ (allow multiple hyphens)
	comment_pat = re.compile(r'/\-+.*?\-+/', re.DOTALL)
	m = comment_pat.search(segment)
	comment = ''
	if m:
		comment = m.group(0).strip()
		# remove the comment from the segment
		segment = segment[:m.start()] + segment[m.end():]

	# Now find the first non-empty line after the comment
	lines = [ln for ln in segment.splitlines()]
	# strip leading empty lines
	while lines and lines[0].strip() == '':
		lines.pop(0)

	type_word = ''
	output_raw = ''
	if lines:
		first_line = lines[0].strip()
		m2 = re.match(r"(\S+)", first_line)
		if m2:
			type_word = m2.group(1)
		# The output should include the first non-empty line and the rest
		output_raw = '\n'.join(lines).strip()
	else:
		output_raw = ''

	# Collapse whitespace to single spaces and escape
	comment_out = escape_text(' '.join(comment.split())) if comment else ''
	output_out = escape_text(' '.join(output_raw.split())) if output_raw else ''

	return comment_out, type_word, output_out


def process_file(path_in: str, out_dir: str):
	with open(path_in, 'r', encoding='utf-8') as f:
		text = f.read()

	# Find all occurrences of marker '--666'
	marker = '--666'
	positions = [m.start() for m in re.finditer(re.escape(marker), text)]
	items = []
	for i, pos in enumerate(positions):
		start = pos + len(marker)
		end = positions[i+1] if i+1 < len(positions) else len(text)
		segment = text[start:end].strip()
		comment, type_word, output = split_segment(segment)
		items.append({
			'comment': comment,
			'type': type_word,
			'output': output,
		})

	# Write JSON
	base = os.path.splitext(os.path.basename(path_in))[0]
	out_path = os.path.join(out_dir, base + '.json')
	os.makedirs(out_dir, exist_ok=True)
	with open(out_path, 'w', encoding='utf-8') as out:
		# Write one JSON object per line. If no items, write an empty file.
		if not items:
			out.write('')
		elif len(items) == 1:
			out.write(json.dumps(items[0], ensure_ascii=False))
		else:
			for obj in items:
				out.write(json.dumps(obj, ensure_ascii=False) + '\n')


def main():
	root = os.path.dirname(__file__) or '.'
	input_dir = os.path.join(root, 'input')
	output_dir = os.path.join(root, 'output')

	files = glob(os.path.join(input_dir, '*.lean'))
	for fpath in files:
		process_file(fpath, output_dir)


if __name__ == '__main__':
	main()

