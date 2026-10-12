"""Rebuild diagrams with distinct named identifiers and visible input provenance."""
from pathlib import Path
from html import escape
import re

OUT = Path(__file__).resolve().parents[1] / 'site/assets/create-time-diagrams'
INK = '#223442'; GOLD = '#79520e'; GOLD_BG = '#fff4d7'
PURPLE = '#70459c'; PURPLE_BG = '#f3edfc'
ORANGE = '#a13d0b'; ORANGE_BG = '#fff0e3'; GRAY = '#546573'
POSITIONS = (
    {'key': 'R', 'card': 'A', 'ja': '赤い位置', 'en': 'Red position', 'ink': '#b13434', 'bg': '#fff0ee', 'shape': 'circle'},
    {'key': 'B', 'card': 'B', 'ja': '青い位置', 'en': 'Blue position', 'ink': '#145b93', 'bg': '#e8f3ff', 'shape': 'triangle'},
    {'key': 'G', 'card': 'C', 'ja': '緑の位置', 'en': 'Green position', 'ink': '#25723f', 'bg': '#ecf7ec', 'shape': 'diamond'},
)
COLOUR_NAMES = {'ja': {'R': '赤', 'B': '青', 'G': '緑'}, 'en': {'R': 'red', 'B': 'blue', 'G': 'green'}}


def expanded_labels(value, lang):
    return re.sub(r'([cTτ])_([RBG])', lambda m: m[1] + '_' + COLOUR_NAMES[lang][m[2]], value)


def labelled_text(value, size, lang):
    """Color source labels while retaining separate card/input identifiers."""
    colors = {p['key']: p['ink'] for p in POSITIONS}
    def subscript(match):
        base, label = match.groups()
        color = f' fill="{colors[label]}"' if base in 'cTτ' and label in colors else ''
        shown = COLOUR_NAMES[lang][label] if base in 'cTτ' and label in colors else label
        return base + f'<tspan font-size="68%" baseline-shift="{-size * .20:g}"{color}>' + shown + '</tspan>'
    return re.sub(r'([crbTτ])_([A-Z])', subscript, escape(value))


class Figure:
    def __init__(self, width, height, title, desc, lang):
        self.width = width; self.height = height
        self.lang = lang
        self.parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-labelledby="title desc">',
            f'<title id="title">{escape(title)}</title><desc id="desc">{escape(expanded_labels(desc, lang))}</desc>',
            '<defs><marker id="arrow" markerWidth="9" markerHeight="9" refX="8" refY="4.5" orient="auto" markerUnits="userSpaceOnUse"><path d="M0 0L9 4.5L0 9Z" fill="#546573"/></marker></defs>',
            '<style>text{font-family:"Hiragino Sans","Noto Sans CJK JP",Arial,sans-serif} .symbol{font-family:"Times New Roman",serif}</style>',
            f'<rect width="{width}" height="{height}" rx="16" fill="white"/>']

    def text(self, x, y, text, size=24, fill=INK, weight=400, anchor='start', symbol=False):
        self.parts.append(f'<text x="{x}" y="{y}" font-size="{size}" fill="{fill}" font-weight="{weight}" text-anchor="{anchor}"' + (' class="symbol"' if symbol else '') + f'>{labelled_text(text, size, self.lang)}</text>')

    def rect(self, x, y, w, h, fill='white', stroke=GRAY, r=10, sw=2):
        self.parts.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{r}" fill="{fill}" stroke="{stroke}" stroke-width="{sw}"/>')

    def line(self, x1, y1, x2, y2, arrow=False, stroke=GRAY):
        self.parts.append(f'<path d="M{x1} {y1}L{x2} {y2}" fill="none" stroke="{stroke}" stroke-width="2.5"' + (' marker-end="url(#arrow)"' if arrow else '') + '/>')

    def token(self, x, y, pos, r=39, size=31):
        paint = f'fill="{pos["bg"]}" stroke="{pos["ink"]}" stroke-width="3"'
        rx = self.token_radius(pos, r)
        if pos['shape'] == 'circle':
            self.parts.append(f'<circle cx="{x}" cy="{y}" r="{r}" {paint}/>')
        elif pos['shape'] == 'triangle':
            self.parts.append(f'<path d="M{x} {y-r}L{x+rx} {y+r}L{x-rx} {y+r}Z" {paint}/>')
        else:
            self.parts.append(f'<path d="M{x} {y-r}L{x+rx} {y}L{x} {y+r}L{x-rx} {y}Z" {paint}/>')
        offset = 13 if pos['shape'] == 'triangle' else (2 if self.lang == 'en' else 8)
        if self.lang == 'en':
            size = min(size, 25)
        self.text(x, y + offset, 'c_' + pos['key'], size, pos['ink'], 600, 'middle', True)

    def token_radius(self, pos, r):
        if self.lang == 'en':
            return r * {'circle': 1, 'triangle': 1.25, 'diamond': 1.3}[pos['shape']]
        return r

    def legend(self, y, ja):
        labels = ['赤 ●', '青 ▲', '緑 ◆'] if ja else ['red circle', 'blue triangle', 'green diamond']
        for x, pos, label in zip([28, 195, 398], POSITIONS, labels):
            self.text(x, y, label, 21, pos['ink'])

    def save(self, name):
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / name).write_text('\n'.join(self.parts + ['</svg>']))


def records(lang):
    ja = lang == 'ja'
    title = '色で見分ける入力と、名前で見分ける記録' if ja else 'Coloured inputs and named record cards'
    desc = '赤丸の入力c_R、青三角の入力c_B、緑菱形の入力c_Gを、それぞれカードAの記録r_A、カードBの記録r_B、カードCの記録r_Cが指定する。スイッチ入力b_A、b_B、b_Cの状態は閉、開、閉。線は対応を示す。' if ja else 'The red-circle input c_R, blue-triangle input c_B and green-diamond input c_G are referenced by record cards A, B and C, named r_A, r_B and r_C. Their switch inputs b_A, b_B and b_C have states Closed, Open and Closed. Lines show recorded references.'
    f = Figure(800, 790, title, desc, lang)
    f.text(28, 42, title, 28, INK, 700)
    f.legend(80, ja)
    f.text(136, 126, 'カウンタ入力' if ja else 'Counter input', 23, INK, 700, 'middle')
    f.text(325, 126, 'メモリが保持する記録カード' if ja else 'A record card retained in memory', 23, GOLD, 700)
    for row, pos in enumerate(POSITIONS):
        y = 151 + row * 190
        f.token(136, y + 53, pos, 43)
        f.text(136, y + 125, '供給元 K' if ja else 'Source K', 21, INK, 400, 'middle')
        f.text(136, y + 157, pos[lang], 23, pos['ink'], 700, 'middle')
        f.line(136 + f.token_radius(pos, 43) + 7, y + 53, 325, y + 53)
        f.text(252, y + 29, '対応' if ja else 'reference', 19, GRAY, 400, 'middle')
        f.rect(325, y, 447, 169, GOLD_BG, GOLD, 8)
        f.rect(342, y + 13, 87, 44, 'white', GOLD, 4)
        f.text(386, y + 43, 'r_' + pos['card'], 30, GOLD, 700, 'middle', True)
        f.text(450, y + 42, ('記録カード ' if ja else 'Record card ') + pos['card'], 23, GOLD, 700)
        f.text(346, y + 90, ('カウンタ：K / ' if ja else 'Counter: K / ') + pos[lang] + ' / c_' + pos['key'], 21, INK)
        value = ('開' if pos['key'] == 'B' else '閉') if ja else ('Open' if pos['key'] == 'B' else 'Closed')
        f.text(346, y + 126, ('スイッチ入力：' if ja else 'Switch input: ') + 'b_' + pos['card'], 22, INK)
        f.text(346, y + 157, ('その状態：' if ja else 'Its state: ') + value, 22, INK)
    f.text(28, 766, '線は、各記録がどの入力を指定しているかを示す。' if ja else 'Each line identifies the input referenced by that record.', 22, GRAY)
    f.save(f'records-{lang}.svg')


def construction(lang):
    ja = lang == 'ja'
    title = '赤・青・緑の入力から、それぞれに割り当てる実数値へ' if ja else 'From coloured inputs to assigned real values'
    desc = '赤丸c_R、青三角c_B、緑菱形c_Gは、別々の同値類T_R、T_B、T_Gに属する。各囲みの中には元の入力を表示する。それぞれ順序座標[T_R]、[T_B]、[T_G]へ写し、実数値τ_R、τ_B、τ_Gを割り当てる。' if ja else 'The red-circle input c_R, blue-triangle input c_B and green-diamond input c_G belong to separate classes T_R, T_B and T_G. Each class enclosure retains its original input. They map to order coordinates [T_R], [T_B] and [T_G] and then to assigned real values τ_R, τ_B and τ_G.'
    f = Figure(1000, 745, title, desc, lang)
    f.text(28, 42, title, 28, INK, 700)
    f.legend(81, ja)
    for x, label, colour in [(108, '入力' if ja else 'Input', INK), (339, '同値類' if ja else 'Equivalence class', PURPLE), (592, '順序座標' if ja else 'Order coordinate', GRAY), (859, '割り当てる実数値' if ja else 'Assigned real value', ORANGE)]:
        f.text(x, 125, label, 22, colour, 700, 'middle')
    for row, pos in enumerate(POSITIONS):
        y = 154 + row * 173
        key = pos['key']
        f.token(108, y + 68, pos, 43)
        f.text(108, y + 138, pos[lang], 21, pos['ink'], 600, 'middle')
        f.line(108 + f.token_radius(pos, 43) + 6, y + 68, 220, y + 68, True)
        f.rect(230, y, 218, 140, PURPLE_BG, PURPLE, 25, 3)
        f.text(339, y + 34, 'T_' + key, 30, PURPLE, 700, 'middle', True)
        f.token(339, y + 91, pos, 32, 27)
        f.text(285, y + 103, '{', 44, PURPLE, 400, 'middle', True)
        f.text(393, y + 103, '}', 44, PURPLE, 400, 'middle', True)
        f.line(455, y + 68, 508, y + 68, True)
        f.rect(518, y + 30, 148, 77, '#f1f4f6', GRAY, 4, 2)
        f.text(592, y + 79, '[T_' + key + ']', 36, GRAY, 600, 'middle', True)
        f.line(674, y + 68, 756, y + 68, True)
        f.rect(766, y + 7, 196, 122, ORANGE_BG, ORANGE, 3, 3)
        f.rect(774, y + 15, 180, 106, 'white', ORANGE, 1, 1)
        f.text(863, y + 64, 'τ_' + key, 48, ORANGE, 700, 'middle', True)
        f.text(863, y + 112, '実数値' if ja else 'real value', 18, ORANGE, 400, 'middle')
    f.text(28, 692, '入力を類にまとめる → 順序座標へ写す → 実数値を割り当てる' if ja else 'Group inputs into classes → map to order coordinates → assign real values', 22, INK)
    f.text(28, 728, '囲みの中の色と形で、元の入力を追える。' if ja else 'The colour and shape inside each class identify its original input.', 22, INK)
    f.save(f'construction-{lang}.svg')


def merging(lang):
    ja = lang == 'ja'
    title = '状態値の一致でまとめると、この例では順序が壊れる' if ja else 'Merging by switch value breaks the order here'
    desc = '赤の類T_Rから青の類T_B、青の類T_Bから緑の類T_Gへ関係がある。赤と緑に対応する状態がともに閉だからと同じ集合Mへまとめると、MからT_BとT_BからMの両方が残る。異なる位置を区別した順序の条件を満たせない。' if ja else 'The relation runs from the red class T_R to the blue class T_B and from the blue class T_B to the green class T_G. Merging the red and green inputs into M because their recorded switch states are both Closed leaves both directions between M and T_B, violating the order conditions while they remain distinct.'
    f = Figure(800, 570, title, desc, lang)
    f.text(28, 40, title, 26, INK, 700)
    f.legend(77, ja)
    f.text(28, 112, 'この例で構成した順序' if ja else 'The order constructed in this example', 22, INK, 700)
    for pos, x in zip(POSITIONS, [128, 400, 672]):
        f.rect(x - 89, 129, 178, 90, PURPLE_BG, PURPLE, 18, 3)
        f.text(x - 40, 181, 'T_' + pos['key'], 25 if lang == 'en' else 30, PURPLE, 600, 'middle', True)
        f.token(x + 42, 174, pos, 30, 22 if lang == 'en' else 25)
    f.line(224, 174, 301, 174, True)
    f.line(496, 174, 573, 174, True)
    f.text(28, 259, 'ともに「閉」だからと、赤と緑の入力を M にまとめた場合' if ja else 'Suppose red and green are merged into M', 22, INK, 700)
    if not ja:
        f.text(28, 291, 'because both recorded switch states are Closed', 22, INK)
    f.rect(48, 315, 247, 143, PURPLE_BG, PURPLE, 24, 3)
    f.text(171, 354, 'M', 31, PURPLE, 700, 'middle', True)
    f.token(118, 408, POSITIONS[0], 32, 27)
    f.token(224, 408, POSITIONS[2], 32, 27)
    f.rect(546, 315, 205, 143, PURPLE_BG, PURPLE, 24, 3)
    f.text(648, 354, 'T_B', 31, PURPLE, 700, 'middle', True)
    f.token(648, 408, POSITIONS[1], 32, 27)
    f.line(303, 359, 536, 359, True)
    f.text(420, 340, 'M → T_B', 23, GRAY, 400, 'middle', True)
    f.line(537, 434, 305, 434, True)
    f.text(420, 416, 'T_B → M', 23, GRAY, 400, 'middle', True)
    f.text(28, 504, 'M と T_B が異なるのに、関係を両方向へたどれる。' if ja else 'M and T_B are distinct, yet the relation runs in both directions.', 22, INK, 700)
    f.text(28, 543, 'このまとめ方では、異なる位置の順序を保てない。' if ja else 'This merger fails to preserve the order of distinct positions.', 22, INK)
    f.save(f'merging-{lang}.svg')


if __name__ == '__main__':
    for language in ('ja', 'en'):
        records(language)
        construction(language)
        merging(language)
    print('Generated bilingual named-label diagrams.')
