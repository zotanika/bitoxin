#!/usr/bin/env python3
"""Render the maintained Korean Markdown source with embedded Korean fonts.

Requires reportlab. BITOXIN_KOREAN_FONT may point to a distributable TrueType font
on non-macOS hosts. No original attachment or network is required to regenerate.
"""
from pathlib import Path
import os
import re
from html import escape
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle, Flowable,
)

ROOT = Path(__file__).resolve().parents[1]
FONT = os.environ.get('BITOXIN_KOREAN_FONT', '/System/Library/Fonts/Supplemental/AppleGothic.ttf')
pdfmetrics.registerFont(TTFont('KR', FONT))
pdfmetrics.registerFontFamily('KR', normal='KR', bold='KR', italic='KR', boldItalic='KR')
NAVY = colors.HexColor('#122B40')
TEAL = colors.HexColor('#007F86')
INK = colors.HexColor('#203344')
MUTED = colors.HexColor('#617685')
PALE = colors.HexColor('#EDF5F6')
PAPER = colors.HexColor('#F5F7F9')
GOLD = colors.HexColor('#D7AF65')
W, H = A4
MARGIN = 48
CONTENT = W - 2 * MARGIN

styles = {
    'body': ParagraphStyle('body', fontName='KR', fontSize=10, leading=15.5,
                           textColor=INK, spaceAfter=8, wordWrap='CJK'),
    'h1': ParagraphStyle('h1', fontName='KR', fontSize=21, leading=29,
                         textColor=NAVY, spaceAfter=19, keepWithNext=True),
    'h2': ParagraphStyle('h2', fontName='KR', fontSize=14, leading=20,
                         textColor=NAVY, spaceBefore=9, spaceAfter=9, keepWithNext=True),
    'h3': ParagraphStyle('h3', fontName='KR', fontSize=11.5, leading=17,
                         textColor=TEAL, spaceBefore=9, spaceAfter=7, keepWithNext=True),
    'cell': ParagraphStyle('cell', fontName='KR', fontSize=9, leading=13.5,
                           textColor=INK, wordWrap='CJK'),
    'th': ParagraphStyle('th', fontName='KR', fontSize=9, leading=13.5,
                         textColor=colors.white, wordWrap='CJK'),
    'code': ParagraphStyle('code', fontName='Courier', fontSize=8, leading=12,
                           textColor=NAVY, wordWrap='CJK'),
    'ref': ParagraphStyle('ref', fontName='KR', fontSize=8.1, leading=11.3,
                          textColor=INK, spaceAfter=4, wordWrap='CJK'),
    'quote': ParagraphStyle('quote', fontName='KR', fontSize=10, leading=15.5,
                            textColor=NAVY, wordWrap='CJK'),
}


def markup(s):
    s = escape(s)
    s = re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', s)
    s = re.sub(r'`([^`]+)`', r'<font color="#007F86">\1</font>', s)
    if s.startswith('https://'):
        s = '<link href="' + s + '" color="#007F86">' + s + '</link>'
    return s


def boxed(text, kind='quote'):
    t = Table([[Paragraph(text, styles[kind])]], colWidths=[CONTENT])
    t.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, -1), PALE if kind == 'quote' else PAPER),
        ('BOX', (0, 0), (-1, -1), .4, colors.HexColor('#D5E3E6')),
        ('LEFTPADDING', (0, 0), (-1, -1), 12),
        ('RIGHTPADDING', (0, 0), (-1, -1), 12),
        ('TOPPADDING', (0, 0), (-1, -1), 10),
        ('BOTTOMPADDING', (0, 0), (-1, -1), 10),
    ]))
    return t


class Mechanism(Flowable):
    def __init__(self):
        super().__init__()
        self.width, self.height = CONTENT, 120

    def draw(self):
        c = self.canv
        gap = 18
        bw = (CONTENT - 2 * gap) / 3
        heads = ['QA 시나리오', 'BITOXIN 프로브', '외부 관측과 판정']
        rows = [
            ['sleep / wakeup', '제품 동작 · 부하', '실제 상태 전이를 확인'],
            ['의존 계산 + private 버퍼', '중단 · 상태 보존 · 재개', '기대값과 관측값 비교'],
            ['오류 기록 · 제품 검사', 'serial / pstore / watchdog', '원인 분석과 재현'],
        ]
        for i in range(3):
            x = i * (bw + gap)
            c.setFillColor(PALE)
            c.roundRect(x, 19, bw, 94, 5, fill=1, stroke=0)
            c.setFillColor(TEAL)
            c.rect(x, 108, bw, 5, fill=1, stroke=0)
            c.setFont('KR', 10)
            c.setFillColor(NAVY)
            c.drawCentredString(x + bw / 2, 90, heads[i])
            c.setFont('KR', 8.2)
            for j, line in enumerate(rows[i]):
                c.drawCentredString(x + bw / 2, 70 - j * 15, line)
            if i < 2:
                xx = x + bw + 4
                c.setStrokeColor(TEAL)
                c.setLineWidth(1)
                c.line(xx, 65, xx + 10, 65)
                c.line(xx + 6, 68, xx + 10, 65)
                c.line(xx + 6, 62, xx + 10, 65)
        c.setFont('KR', 8)
        c.setFillColor(MUTED)
        c.drawString(0, 4, '그림 1. 환경 생성, 정합성 검사, 실패 관측을 분리한 QA 구성')


def page(canvas, doc):
    canvas.saveState()
    if doc.page == 1:
        canvas.setFillColor(NAVY)
        canvas.rect(0, H - 238, W, 238, fill=1, stroke=0)
        canvas.setFillColor(GOLD)
        canvas.rect(MARGIN, H - 58, 34, 4, fill=1, stroke=0)
        canvas.setFont('Helvetica', 9)
        canvas.setFillColor(colors.HexColor('#C5D8E4'))
        canvas.drawString(MARGIN + 44, H - 60, 'SYSTEM INTEGRITY / TECHNICAL WHITE PAPER')
        canvas.setFillColor(colors.white)
        canvas.setFont('Helvetica-Bold', 40)
        canvas.drawString(MARGIN, H - 116, 'BITOXIN 2')
        canvas.setFont('KR', 19)
        canvas.drawString(MARGIN, H - 154, '상태의 의존 관계와')
        canvas.drawString(MARGIN, H - 184, '오류 관측을 설계하는 QA')
        canvas.setFillColor(colors.HexColor('#C5D8E4'))
        canvas.setFont('KR', 9)
        canvas.drawString(MARGIN, H - 217, '2026.10.05  /  구현 버전 2.0  /  한국어 기술 백서')
    else:
        canvas.setFillColor(TEAL)
        canvas.setFont('Helvetica-Bold', 9)
        canvas.drawString(MARGIN, H - 29, 'BITOXIN 2')
        canvas.setFillColor(MUTED)
        canvas.setFont('KR', 8)
        canvas.drawRightString(W - MARGIN, H - 29, '설계 · 검증 증거 · QA 적용')
        canvas.setStrokeColor(colors.HexColor('#D7E1E6'))
        canvas.line(MARGIN, H - 37, W - MARGIN, H - 37)
    canvas.setStrokeColor(colors.HexColor('#D7E1E6'))
    canvas.line(MARGIN, 36, W - MARGIN, 36)
    canvas.setFillColor(MUTED)
    canvas.setFont('KR', 7.5)
    canvas.drawString(MARGIN, 23, 'BITOXIN 기술 백서  /  실제 보드 적용 효과는 별도 검증 대상')
    canvas.setFont('Helvetica', 8)
    canvas.drawRightString(W - MARGIN, 23, f'{doc.page:02d}')
    canvas.restoreState()


def parse_section(text, reference=False):
    lines = text.strip().splitlines()
    flow = []
    i = 0
    body = styles['ref' if reference else 'body']
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
        if line.startswith('```'):
            block = []
            i += 1
            while i < len(lines) and not lines[i].startswith('```'):
                block.append(escape(lines[i]).replace(' ', '&nbsp;'))
                i += 1
            flow += [boxed('<br/>'.join(block), 'code'), Spacer(1, 10)]
        elif line.startswith('|'):
            data = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                cells = [c.strip() for c in lines[i].strip().strip('|').split('|')]
                if not all(re.fullmatch(r'[-: ]+', c) for c in cells):
                    sty = styles['th' if not data else 'cell']
                    data.append([Paragraph(markup(c), sty) for c in cells])
                i += 1
            i -= 1
            widths = [CONTENT * .27, CONTENT * .73] if len(data[0]) == 2 else [CONTENT / len(data[0])] * len(data[0])
            table = Table(data, colWidths=widths, repeatRows=1, hAlign='LEFT')
            table.setStyle(TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), NAVY),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [PAPER, colors.white]),
                ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                ('LEFTPADDING', (0, 0), (-1, -1), 9),
                ('RIGHTPADDING', (0, 0), (-1, -1), 9),
                ('TOPPADDING', (0, 0), (-1, -1), 7),
                ('BOTTOMPADDING', (0, 0), (-1, -1), 7),
                ('LINEBELOW', (0, -1), (-1, -1), .4, colors.HexColor('#CEDCE2')),
            ]))
            flow += [table, Spacer(1, 11)]
        elif line == '[[mechanism]]':
            flow += [Mechanism(), Spacer(1, 5)]
        elif line.startswith('# '):
            flow.append(Paragraph(markup(line[2:]), styles['h1']))
        elif line.startswith('## '):
            flow.append(Paragraph(markup(line[3:]), styles['h2']))
        elif line.startswith('### '):
            flow.append(Paragraph(markup(line[4:]), styles['h3']))
        elif line.startswith('> '):
            flow += [boxed(markup(line[2:])), Spacer(1, 11)]
        elif line.startswith('- ') or re.match(r'^\d+\. ', line):
            prefix, content = line.split(' ', 1)
            bullet = '-' if prefix == '-' else prefix
            sty = ParagraphStyle('list', parent=body, leftIndent=13, firstLineIndent=0,
                                 bulletIndent=0, bulletFontName='KR', bulletFontSize=body.fontSize)
            flow.append(Paragraph(markup(content), sty, bulletText=bullet))
        else:
            flow.append(Paragraph(markup(line), body))
        i += 1
    return flow


def main():
    source = ROOT / 'docs/whitepaper.ko.md'
    out = ROOT / 'output/pdf/bitoxin-whitepaper-ko.pdf'
    sections = source.read_text().split('---page---')
    story = [Spacer(1, 202)]
    cover = sections[0].splitlines()
    # Cover title/subtitle/date are drawn consistently in the page template.
    start = next(i for i, line in enumerate(cover) if line.startswith('**검사'))
    story.extend(parse_section('\n'.join(cover[start:])))
    for section in sections[1:]:
        story.append(PageBreak())
        story.extend(parse_section(section, reference=section.strip().startswith('# 참고자료')))
    out.parent.mkdir(parents=True, exist_ok=True)
    doc = SimpleDocTemplate(str(out), pagesize=A4, rightMargin=MARGIN, leftMargin=MARGIN,
                            topMargin=55, bottomMargin=51, title='BITOXIN 2 - 상태 의존성과 오류 관측을 설계하는 QA',
                            author='BITOXIN', subject='시스템 상태 손상 검출 설계와 QA 검증 방법')
    doc.build(story, onFirstPage=page, onLaterPages=page)
    print(out)

if __name__ == '__main__':
    main()
