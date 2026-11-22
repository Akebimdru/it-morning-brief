"""IT 모닝 브리핑: 뉴스·인터뷰·논문을 모아 '중요도'로 순위를 매기고 HTML로 만든다.

수집 기간: 전날 07:00 ~ 당일 07:00 (KST).  실행 시각과 상관없이 가장 최근의 07:00이 끝점이다.

중요도 신호
  뉴스   - 같은 이야기를 다룬 매체 수 (제목 유사도·URL로 묶음)
         - Techmeme(업계 편집자 큐레이션) 선정, Hacker News 점수, Google News 관련 기사 수
         - 빅테크 총수 인터뷰/발언, 최신성
  논문   - 게재 저널 (Nature/Science 및 자매지)
         - Hugging Face Daily Papers 추천 수, 유명 연구소 여부
         - Hacker News 점수, 학회 채택 표기(arXiv comment), 뉴스에서 다뤄졌는지

출력: 분야별 상위 10개 + 전체 상위 10개.
표준 라이브러리만 사용한다.
  python fetch_news.py                       # 평소 실행
  python fetch_news.py --end 2026-11-20T07:00 --dry   # 특정 기간 테스트(파일 안 씀)
"""
from __future__ import annotations

import argparse
import html
import json
import math
import re
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, time as dtime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "archive"
TOP_N = 10
MAX_UNSIGNALED = 3   # 아무 신호 없는 arXiv 논문은 탭마다 최대 3개
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PersonalNewsBrief/1.0"
KST = timezone(timedelta(hours=9))
UTC = timezone.utc

# ---------------------------------------------------------------- 소스
FEEDS = {
    "The Verge": "https://www.theverge.com/rss/index.xml",
    "TechCrunch": "https://techcrunch.com/feed/",
    "Ars Technica": "https://feeds.arstechnica.com/arstechnica/index",
    "IEEE Spectrum": "https://spectrum.ieee.org/feeds/feed.rss",
    "The Register": "https://www.theregister.com/headlines.atom",
    "Tom's Hardware": "https://www.tomshardware.com/feeds/all",
    "SemiAnalysis": "https://www.semianalysis.com/feed",
    "ServeTheHome": "https://www.servethehome.com/feed/",
    "The Next Platform": "https://www.nextplatform.com/feed/",
    "Light Reading": "https://www.lightreading.com/rss.xml",
    "The Robot Report": "https://www.therobotreport.com/feed/",
    "전자신문": "https://rss.etnews.com/Section901.xml",
    "디일렉": "http://www.thelec.kr/rss/allArticle.xml",
    "ZDNet Korea": "https://feeds.feedburner.com/zdkorea",
}
TECHMEME_FEED = "https://www.techmeme.com/feed.xml"
TECHMEME_RIVER = "https://www.techmeme.com/river"

JOURNALS = {
    "Nature": "https://www.nature.com/nature.rss",
    "Science": "https://www.science.org/action/showFeed?type=etoc&feed=rss&jc=science",
    "Nature Electronics": "https://www.nature.com/natelectron.rss",
    "Nature Machine Intelligence": "https://www.nature.com/natmachintell.rss",
    "Nature Photonics": "https://www.nature.com/nphoton.rss",
    "Science Robotics": "https://www.science.org/action/showFeed?type=etoc&feed=rss&jc=scirobotics",
}
JOURNAL_WEIGHT = {"Nature": 2.5, "Science": 2.5}   # 나머지 자매지는 1.8
JOURNAL_CATS = {"Nature Electronics": "반도체·아키텍처", "Nature Machine Intelligence": "AI",
                "Nature Photonics": "통신·전송", "Science Robotics": "로보틱스"}

# AI 논문은 양이 너무 많아 Hugging Face 추천 목록으로 받고, 나머지 분야는 arXiv에서 직접 받는다.
ARXIV_CATS = {"cs.AR": "반도체·아키텍처", "cs.DC": "반도체·아키텍처", "cs.RO": "로보틱스", "cs.NI": "통신·전송"}
VENUE_RE = re.compile(
    r"\b(accepted|to appear|NeurIPS|ICML|ICLR|CVPR|ICCV|ECCV|ACL|EMNLP|ISCA|MICRO|HPCA|ASPLOS|DAC|ISSCC|VLSI|"
    r"SIGCOMM|NSDI|MobiCom|INFOCOM|OFC|ECOC|ICRA|IROS|RSS|CoRL|Humanoids|OSDI|SOSP|EuroSys|SC ?'?\d\d)\b", re.I)
BIG_LABS = re.compile(r"google|deepmind|openai|anthropic|meta|microsoft|nvidia|apple|amazon|alibaba|qwen|deepseek|"
                      r"bytedance|tencent|mistral|stanford|mit\b|berkeley|tsinghua|allen|ai2|moonshot|zhipu", re.I)
PAPER_HOSTS = ("arxiv.org", "nature.com/articles", "science.org/doi", "openreview.net", "aclanthology.org",
               "dl.acm.org", "ieeexplore.ieee.org", "biorxiv.org", "huggingface.co/papers")

LEADERS = [
    "Jensen Huang", "Sam Altman", "Satya Nadella", "Sundar Pichai", "Mark Zuckerberg",
    "Elon Musk", "Tim Cook", "Dario Amodei", "Lisa Su", "Demis Hassabis", "Andy Jassy",
    "Lip-Bu Tan", "C.C. Wei", "Masayoshi Son", "Cristiano Amon", "Mustafa Suleyman",
]
LEADERS_KO = ["젠슨 황", "올트먼", "나델라", "피차이", "저커버그", "머스크", "팀 쿡",
              "아모데이", "리사 수", "허사비스", "이재용", "최태원", "손정의"]


def _gnews(q: str, ko: bool = False) -> str:
    loc = "hl=ko&gl=KR&ceid=KR:ko" if ko else "hl=en-US&gl=US&ceid=US:en"
    return f"https://news.google.com/rss/search?q={urllib.parse.quote(q)}&{loc}"


GNEWS = {
    "leaders": _gnews("(" + " OR ".join(f'"{n}"' for n in LEADERS[:11]) + ") (interview OR podcast OR keynote) when:2d"),
    "leaders_ko": _gnews("(" + " OR ".join(f'"{n}"' for n in LEADERS_KO) + ") 인터뷰 when:2d", ko=True),
    "transmission": _gnews('("co-packaged optics" OR "optical interconnect" OR 6G OR "subsea cable" OR NVLink OR "silicon photonics" OR "800G" OR "1.6T") when:2d'),
    "robotics": _gnews('(humanoid OR robotaxi OR "physical AI" OR robotics) (Tesla OR Nvidia OR Figure OR Waymo OR Unitree OR "Boston Dynamics" OR Google OR Amazon OR Hyundai) when:2d'),
    "semis_ko": _gnews("(반도체 OR HBM OR 파운드리 OR AI) when:2d", ko=True),
}

# ---------------------------------------------------------------- 분류
CATEGORIES = {
    "AI": [r"\bai\b", r"artificial intelligence", r"openai", r"anthropic", r"\bclaude\b", r"\bgpt", r"gemini",
           r"\bllms?\b", r"deepmind", r"\bagents?\b", r"agentic", r"chatbot", r"machine learning", r"\bmeta ai\b",
           r"xai\b", r"mistral", r"deepseek", r"language models?", r"diffusion", r"reinforcement learning",
           r"transformer", r"multimodal", r"reasoning", r"인공지능", r"생성형", r"\bAI\b", r"에이전트", r"챗봇", r"거대언어모델"],
    "통신·전송": [r"\b5g\b", r"\b6g\b", r"optic", r"photonic", r"fiber", r"ethernet", r"interconnect", r"serdes",
              r"nvlink", r"ucie", r"\bcpo\b", r"co-packaged", r"telecom", r"subsea", r"undersea cable", r"satellite",
              r"starlink", r"wi-?fi", r"broadband", r"spectrum auction", r"\b800g\b", r"1\.6t", r"infiniband",
              r"wireless", r"\bmimo\b", r"transceiver", r"networking", r"\bran\b", r"통신", r"광모듈", r"광통신", r"네트워크 장비", r"위성", r"전송"],
    "반도체·아키텍처": [r"\bchips?\b", r"\bgpus?\b", r"\bcpus?\b", r"\btpus?\b", r"\bnpu", r"semiconductor", r"tsmc",
                 r"\bhbm", r"\bdram\b", r"\bnand\b", r"risc-v", r"\barm\b", r"x86", r"nvidia", r"\bamd\b", r"\bintel\b",
                 r"qualcomm", r"broadcom", r"wafer", r"foundry", r"\b[23]nm\b", r"\b1\.4nm\b", r"packaging",
                 r"blackwell", r"rubin", r"micron", r"asml", r"data ?center", r"supercomputer", r"accelerator",
                 r"transistor", r"\bfpga", r"processor", r"memory", r"cache", r"\bsram\b", r"in-memory computing",
                 r"반도체", r"칩", r"파운드리", r"메모리", r"삼성전자", r"하이닉스", r"엔비디아", r"데이터센터", r"패키징"],
    "빅테크 리더": [re.escape(n.lower()) for n in LEADERS] + [re.escape(n) for n in LEADERS_KO],
    "로보틱스": [r"robot", r"humanoid", r"autonomous", r"self-driving", r"waymo", r"optimus", r"figure ai",
             r"boston dynamics", r"physical ai", r"drone", r"manipulation", r"locomotion", r"embodied",
             r"로봇", r"휴머노이드", r"자율주행", r"피지컬"],
}
CAT_RE = {c: re.compile("|".join(p), re.I) for c, p in CATEGORIES.items()}
INTERVIEW_RE = re.compile(r"interview|podcast|keynote|says|said|told|remarks|인터뷰|대담|기조연설|밝혔|말했", re.I)
JUNK_RE = re.compile(r"\bdeals?\b|% off|half price|discount|\bsale\b|coupon|best .* (to buy|for)|black friday|"
                     r"cyber monday|giveaway|sponsored|특가|할인|이벤트", re.I)

STOP = set("""the a an and or of to in on for with at by from as is are was were be been its it this that
these those into over after about new says said say will can could would should has have had not but
than more most how why what when who which just now up out off amid via vs report reports""".split())


@dataclass
class Item:
    title: str
    link: str
    source: str            # 매체/저널 이름
    feed: str              # 수집 경로: Techmeme, Hacker News, gnews:*, HF, arXiv, 저널명, 매체명
    published: datetime    # 논문은 공개(발표) 시각
    summary: str = ""
    kind: str = "news"     # news | paper
    hn_points: int = 0
    hn_comments: int = 0
    related: int = 0       # Google News 관련 기사 수
    upvotes: int = 0       # Hugging Face 추천 수
    org: str = ""
    authors: list = field(default_factory=list)
    accepted: str = ""     # arXiv comment 속 학회 표기
    base_cats: list = field(default_factory=list)
    tokens: set = field(default_factory=set)


# ---------------------------------------------------------------- 시간
def collection_window(end_override: str | None) -> tuple[datetime, datetime]:
    if end_override:
        end = datetime.fromisoformat(end_override).replace(tzinfo=KST)
    else:
        now = datetime.now(KST)
        end = now.replace(hour=7, minute=0, second=0, microsecond=0)
        if now < end:
            end -= timedelta(days=1)
    return (end - timedelta(days=1)).astimezone(UTC), end.astimezone(UTC)


def et_offset(utc: datetime) -> timedelta:
    """미국 동부 시간 오프셋 (3월 둘째 일요일 ~ 11월 첫째 일요일 서머타임)."""
    y = utc.year
    mar = datetime(y, 3, 8, 7, tzinfo=UTC)
    mar += timedelta(days=(6 - mar.weekday()) % 7)
    nov = datetime(y, 11, 1, 6, tzinfo=UTC)
    nov += timedelta(days=(6 - nov.weekday()) % 7)
    return timedelta(hours=-4) if mar <= utc < nov else timedelta(hours=-5)


def et_to_utc(naive_et: datetime) -> datetime:
    guess = naive_et.replace(tzinfo=UTC) + timedelta(hours=5)
    return naive_et.replace(tzinfo=UTC) - et_offset(guess)


def arxiv_announce(submitted: datetime) -> datetime:
    """arXiv 공개 시각: 평일 14:00 ET 마감분이 그날 20:00 ET에 공개, 금요일 마감분은 일요일 20:00 ET."""
    et = (submitted + et_offset(submitted)).replace(tzinfo=None)
    day = et
    if et.weekday() >= 5 or et.hour >= 14:
        day = et + timedelta(days=1)
        while day.weekday() >= 5:
            day += timedelta(days=1)
    ann_date = day.date() + timedelta(days=2 if day.weekday() == 4 else 0)
    return et_to_utc(datetime.combine(ann_date, dtime(20, 0)))


# ---------------------------------------------------------------- 유틸
def fetch(url: str, timeout: int = 25) -> bytes | None:
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*"})
    for attempt in range(2):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001
            if attempt == 1:
                print(f"  ! {url[:90]} -> {e}", file=sys.stderr)
            time.sleep(2)
    return None


def strip_html(s: str) -> str:
    s = re.sub(r"<[^>]+>", " ", s or "")
    s = html.unescape(s)
    return re.sub(r"\s+", " ", s).strip()


def clip(s: str, n: int = 230) -> str:
    return s if len(s) <= n else s[: n - 1].rstrip() + "…"


def parse_date(s: str | None) -> datetime | None:
    if not s:
        return None
    s = s.strip()
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
        # 날짜만 있는 저널 피드: Nature/Science 는 대략 15:00 UTC 에 공개
        return datetime.fromisoformat(s).replace(hour=15, tzinfo=UTC)
    try:
        d = parsedate_to_datetime(s)
    except Exception:  # noqa: BLE001
        try:
            d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except ValueError:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=KST)
    return d.astimezone(UTC)


def local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def child_text(el: ET.Element, *names: str) -> str:
    for c in el:
        if local(c.tag) in names:
            if local(c.tag) == "link" and c.get("href"):
                return c.get("href")
            return (c.text or "").strip()
    return ""


def tokenize(title: str) -> set:
    words = re.findall(r"[a-z0-9][a-z0-9.\-]+|[가-힣]{2,}", title.lower())
    out = set()
    for w in words:
        w = w.strip(".-")
        if re.match(r"[가-힣]", w) or (len(w) >= 3 and w not in STOP):
            out.add(w)
    return out


def is_paper_link(link: str) -> bool:
    return any(h in link for h in PAPER_HOSTS)


def norm_url(u: str) -> str:
    m = re.search(r"arxiv\.org/(?:abs|pdf|html)/(\d{4}\.\d{4,5})", u) or re.search(r"huggingface\.co/papers/(\d{4}\.\d{4,5})", u)
    if m:
        return "arxiv:" + m.group(1)
    p = urllib.parse.urlparse(u)
    # 쿼리 문자열이 기사 ID인 사이트(articleView.html?idxno=…)가 있어 쿼리도 유지
    q = "&".join(kv for kv in p.query.split("&") if kv and not kv.startswith(("utm_", "oc=", "ref=", "af=")))
    return (p.netloc.replace("www.", "") + p.path.rstrip("/") + ("?" + q if q else "")).lower()


# ---------------------------------------------------------------- 수집: 뉴스
def parse_feed(name: str, raw: bytes, kind: str = "news") -> list[Item]:
    try:
        root = ET.fromstring(raw)
    except ET.ParseError:
        try:
            root = ET.fromstring(raw.decode("utf-8", "ignore").encode())
        except ET.ParseError as e:
            print(f"  ! parse {name}: {e}", file=sys.stderr)
            return []
    out = []
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        title = strip_html(child_text(el, "title"))
        link = child_text(el, "link") or child_text(el, "guid", "id") or el.get(
            "{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about", "")
        desc_raw = child_text(el, "description", "summary", "encoded", "content")
        pub = parse_date(child_text(el, "pubDate", "published", "updated", "date"))
        if not title or not link or not pub:
            continue
        source, summary, related, authors = name, strip_html(desc_raw), 0, []
        if name.startswith("gnews"):
            m = re.match(r"(.*)\s+-\s+([^-]+)$", title)
            if m:
                title, source = m.group(1).strip(), m.group(2).strip()
            related = max(0, len(re.findall(r"<li", desc_raw, re.I)) - 1)
            summary = ""
        if kind == "paper":
            authors = [strip_html(c.text or "") for c in el if local(c.tag) == "creator"][:4]
            summary = re.sub(r"^(Nature|Science)[^.]*?, Published online:.*?;\s*doi:\S+\s*", "", summary)
            summary = re.sub(r"^Science(?: Robotics)?, Volume \d+, Issue \d+, \w+ \d{4}\.\s*", "", summary)
        it = Item(title=title, link=link, source=source, feed=name, published=pub, summary=clip(summary),
                  related=related, base_cats=[JOURNAL_CATS[name]] if name in JOURNAL_CATS else [], kind=kind if kind == "paper" or not is_paper_link(link) else "paper",
                  authors=authors, tokens=tokenize(title))
        out.append(it)
    return out


def fetch_techmeme() -> list[Item]:
    """River 페이지는 최근 며칠치 Techmeme 선정 기사 전체(시각 포함)를 보여 준다. RSS는 요약용."""
    summaries = {}
    raw = fetch(TECHMEME_FEED)
    if raw:
        for m in re.finditer(r"<description><!\[CDATA\[(.*?)\]\]></description>", raw.decode("utf-8", "ignore"), re.S):
            d = m.group(1)
            a = re.search(r'<B><A HREF="([^"]+)"', d, re.I)
            s = re.search(r"&mdash;(?:&nbsp;)?\s*(.*?)</P>", d, re.S | re.I)
            if a and s:
                summaries[norm_url(html.unescape(a.group(1)))] = clip(strip_html(s.group(1)))
    raw = fetch(TECHMEME_RIVER)
    if not raw:
        return []
    page = raw.decode("utf-8", "ignore")
    parts = re.split(r"<H2>([^<]+)</H2>", page)
    out = []
    for date_str, body in zip(parts[1::2], parts[2::2]):
        try:
            day = datetime.strptime(date_str.strip(), "%B %d, %Y")
        except ValueError:
            continue
        for m in re.finditer(r'<tr class="ritem"><td>([^<&]+?)\s*&nbsp;.*?<cite>(.*?)</cite>.*?<a href="([^"]+)">(.*?)</a></td></tr>',
                             body, re.S):
            try:
                t = datetime.strptime(m.group(1).strip(), "%I:%M %p")
            except ValueError:
                continue
            pub = et_to_utc(day.replace(hour=t.hour, minute=t.minute))
            source = strip_html(m.group(2)).rstrip(":").split("/")[-1].strip() or "Techmeme"
            link = html.unescape(m.group(3))
            title = strip_html(m.group(4))
            out.append(Item(title=title, link=link, source=source, feed="Techmeme", published=pub,
                            summary=summaries.get(norm_url(link), ""),
                            kind="paper" if is_paper_link(link) else "news", tokens=tokenize(title)))
    return out


def fetch_hn(start: datetime, end: datetime) -> list[Item]:
    url = ("https://hn.algolia.com/api/v1/search?tags=story&hitsPerPage=300"
           f"&numericFilters=created_at_i>{int(start.timestamp())},created_at_i<{int(end.timestamp())},points>40")
    raw = fetch(url)
    if not raw:
        return []
    out = []
    for h in json.loads(raw).get("hits", []):
        link = h.get("url") or f"https://news.ycombinator.com/item?id={h['objectID']}"
        dom = urllib.parse.urlparse(link).netloc.replace("www.", "")
        out.append(Item(title=h["title"], link=link, source=dom or "Hacker News", feed="Hacker News",
                        published=datetime.fromtimestamp(h["created_at_i"], UTC),
                        hn_points=h.get("points") or 0, hn_comments=h.get("num_comments") or 0,
                        kind="paper" if is_paper_link(link) else "news", tokens=tokenize(h["title"])))
    return out


# ---------------------------------------------------------------- 수집: 논문
def fetch_hf(start: datetime, end: datetime) -> list[Item]:
    out = []
    days = sorted({(start + timedelta(hours=h)).date() for h in range(0, 25, 6)})
    for d in days:
        t = datetime(d.year, d.month, d.day, 12, tzinfo=UTC)  # 그날 목록은 하루 동안 채워지므로 정오로 간주
        if not start <= t < end:
            continue
        raw = fetch(f"https://huggingface.co/api/daily_papers?date={d}&limit=100")
        for e in json.loads(raw) if raw else []:
            p = e.get("paper", {})
            org = (e.get("organization") or p.get("organization") or {}).get("fullname", "") or ""
            title = re.sub(r"\s+", " ", e.get("title") or p.get("title", "")).strip()
            out.append(Item(title=title, link=f"https://arxiv.org/abs/{p['id']}", source="arXiv", feed="HF",
                            published=t, kind="paper", summary=clip(p.get("ai_summary") or e.get("summary", "")),
                            upvotes=p.get("upvotes", 0) or 0, org=org,
                            authors=[a.get("name", "") for a in p.get("authors", [])[:4]],
                            base_cats=["AI"], tokens=tokenize(title)))
    return out


def fetch_arxiv(start: datetime, end: datetime) -> list[Item]:
    lo = (start - timedelta(days=5)).strftime("%Y%m%d%H%M")
    hi = end.strftime("%Y%m%d%H%M")
    q = "(" + " OR ".join(f"cat:{c}" for c in ARXIV_CATS) + f") AND submittedDate:[{lo} TO {hi}]"
    url = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(
        {"search_query": q, "sortBy": "submittedDate", "sortOrder": "descending", "max_results": "2000"})
    raw = fetch(url, timeout=90)
    if not raw:
        return []
    ns = {"a": "http://www.w3.org/2005/Atom", "x": "http://arxiv.org/schemas/atom"}
    out = []
    for e in ET.fromstring(raw).findall("a:entry", ns):
        aid = re.search(r"abs/(\d{4}\.\d{4,5})", e.findtext("a:id", "", ns))
        sub = parse_date(e.findtext("a:published", "", ns))
        if not aid or not sub:
            continue
        ann = arxiv_announce(sub)
        if not start <= ann < end:
            continue
        cats = [c.get("term") for c in e.findall("a:category", ns)]
        prim = (e.find("x:primary_category", ns).get("term") if e.find("x:primary_category", ns) is not None else "")
        base = []
        for c in [prim] + cats:
            if c in ARXIV_CATS and ARXIV_CATS[c] not in base:
                base.append(ARXIV_CATS[c])
        comment = e.findtext("x:comment", "", ns) or ""
        venue = VENUE_RE.search(comment)
        title = re.sub(r"\s+", " ", e.findtext("a:title", "", ns)).strip()
        out.append(Item(title=title, link=f"https://arxiv.org/abs/{aid.group(1)}", source="arXiv", feed="arXiv",
                        published=ann, kind="paper", summary=clip(re.sub(r"\s+", " ", e.findtext("a:summary", "", ns))),
                        authors=[a.findtext("a:name", "", ns) for a in e.findall("a:author", ns)[:4]],
                        accepted=clip(comment, 60) if venue else "", base_cats=base, tokens=tokenize(title)))
    return out


def collect(start: datetime, end: datetime) -> list[Item]:
    jobs = {**FEEDS, **JOURNALS, **{f"gnews:{k}": v for k, v in GNEWS.items()}}
    items: list[Item] = []
    with ThreadPoolExecutor(max_workers=12) as ex:
        extra = {"Techmeme": ex.submit(fetch_techmeme), "Hacker News": ex.submit(fetch_hn, start, end),
                 "HF Daily Papers": ex.submit(fetch_hf, start, end), "arXiv": ex.submit(fetch_arxiv, start, end)}
        results = dict(zip(jobs, ex.map(fetch, jobs.values())))
        for name, raw in results.items():
            got = parse_feed(name, raw, "paper" if name in JOURNALS else "news") if raw else []
            items += got
        for name, fut in extra.items():
            try:
                items += fut.result()
            except Exception as e:  # noqa: BLE001
                print(f"  ! {name}: {e}", file=sys.stderr)
    kept = [i for i in items if start <= i.published < end]
    counts: dict[str, int] = {}
    for i in kept:
        k = i.feed.split(":")[0] if not i.feed.startswith("gnews") else "Google News"
        counts[k] = counts.get(k, 0) + 1
    print("  " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items(), key=lambda kv: -kv[1])))
    return kept


# ---------------------------------------------------------------- 묶기·점수
def similar(a: set, b: set) -> bool:
    if not a or not b:
        return False
    shared = len(a & b)
    small = min(len(a), len(b))
    return shared >= 5 or (shared >= 3 and shared / small >= 0.4) or (shared >= 2 and shared / small >= 0.67)


def cluster(items: list[Item]) -> list[list[Item]]:
    order = sorted(items, key=lambda i: (i.feed != "Techmeme", -i.hn_points, -i.upvotes, -i.related))
    clusters: list[tuple[set, list[Item]]] = []
    by_url: dict[str, list[Item]] = {}
    for it in order:
        u = norm_url(it.link)
        if u in by_url:
            by_url[u].append(it)
            continue
        for toks, members in clusters:
            # 대표(첫 기사)와만 비교해 연쇄적으로 엉뚱한 기사가 붙지 않게 한다
            same_outlet = it.feed == members[0].feed and not it.feed.startswith("gnews")
            if not same_outlet and similar(it.tokens, toks):
                members.append(it)
                by_url[u] = members
                break
        else:
            members = [it]
            clusters.append((set(it.tokens), members))
            by_url[u] = members
    return [m for _, m in clusters]


def member_weight(m: Item) -> float:
    if m.feed == "Hacker News":
        return 0.6 * math.log2(1 + m.hn_points / 25)
    if m.feed.startswith("gnews"):
        return 0.3 + 0.2 * min(m.related, 6)
    if m.feed == "Techmeme":
        return 3.0
    if m.feed in JOURNALS:
        return JOURNAL_WEIGHT.get(m.feed, 1.8)
    if m.feed == "HF":
        return 0.4 + math.log2(1 + m.upvotes / 3) + (0.5 if BIG_LABS.search(m.org) else 0)
    if m.feed == "arXiv":
        return 0.4 + (0.8 if m.accepted else 0)
    return {"SemiAnalysis": 1.5, "IEEE Spectrum": 1.2}.get(m.feed, 1.0)


def score(members: list[Item], end: datetime) -> dict:
    main = members[0]
    is_paper = any(m.kind == "paper" for m in members) and main.kind == "paper" or all(m.kind == "paper" for m in members)
    if is_paper:
        # 초록은 'neural network' 같은 일반 용어가 많아 분류가 흐려지므로 제목만 본다
        kw = [c for c in categorize(" ".join(m.title for m in members[:3])) if c != "빅테크 리더"]
        base = [c for m in members for c in m.base_cats]
        cats = list(dict.fromkeys(base + kw))
        interview = False
    else:
        cats = categorize(" ".join(m.title for m in members[:6]))
        full = " ".join(f"{m.title} {m.summary}" for m in members[:4])
        interview = bool(CAT_RE["빅테크 리더"].search(full)) and bool(INTERVIEW_RE.search(full))
        if interview and "빅테크 리더" in cats:
            cats.remove("빅테크 리더")
            cats.insert(0, "빅테크 리더")

    outlets: dict[str, float] = {}
    for m in members:
        # HF 목록과 arXiv 목록은 같은 논문의 두 경로이므로 한 곳으로 센다
        key = "arXiv" if m.feed in ("HF", "arXiv") else (
            m.feed if m.feed in ("Techmeme", "Hacker News") or m.feed in JOURNALS else m.source.lower())
        outlets[key] = max(outlets.get(key, 0), member_weight(m))
    coverage = sum(sorted(outlets.values(), reverse=True)[:8])
    newest = max(m.published for m in members)
    age_h = (end - newest).total_seconds() / 3600
    recency = 1.0 * max(0.0, 1 - age_h / 24)
    s = coverage + recency + (1.5 if interview else 0) + (0.8 if cats else 0)
    signaled = not all(m.feed == "arXiv" and not m.accepted for m in members)
    return {"score": round(s, 2), "cats": cats, "outlets": len(outlets), "interview": interview,
            "newest": newest, "paper": is_paper, "signaled": signaled}


def categorize(text: str) -> list[str]:
    hits = {c: len(r.findall(text)) for c, r in CAT_RE.items()}
    return [c for c, n in sorted(hits.items(), key=lambda kv: -kv[1]) if n > 0]


def select(clusters: list[list[Item]], end: datetime) -> tuple[list[dict], dict[str, list[int]]]:
    scored = []
    for members in clusters:
        info = score(members, end)
        if not info["cats"]:
            continue  # 관심 분야가 아니면 제외
        if not info["paper"] and JUNK_RE.search(members[0].title):
            continue
        scored.append({**info, "members": members})
    scored.sort(key=lambda d: -d["score"])

    def top(pred) -> list[dict]:
        out, weak = [], 0
        for d in scored:
            if not pred(d):
                continue
            if not d["signaled"]:
                if weak >= MAX_UNSIGNALED:
                    continue
                weak += 1
            out.append(d)
            if len(out) >= TOP_N:
                break
        return out

    tabs = {"전체": top(lambda d: True), "논문": top(lambda d: d["paper"])}
    for cat in CATEGORIES:
        tabs[cat] = top(lambda d, c=cat: c in d["cats"][:2])
    stories: list[dict] = []
    index: dict[int, int] = {}
    tab_ids: dict[str, list[int]] = {}
    for name, lst in tabs.items():
        ids = []
        for d in lst:
            if id(d) not in index:
                index[id(d)] = len(stories)
                stories.append(d)
            ids.append(index[id(d)])
        tab_ids[name] = ids
    return stories, tab_ids


# ---------------------------------------------------------------- 출력
def present(d: dict) -> dict:
    members = d["members"]
    news_pref = ["Techmeme"] + list(FEEDS)
    paper_pref = list(JOURNALS) + ["HF", "arXiv", "Techmeme"] + list(FEEDS)

    def rank(m: Item) -> int:
        pref = paper_pref if d["paper"] else news_pref
        if m.feed in pref:
            return pref.index(m.feed)
        return 50 if m.feed == "Hacker News" else 80

    main = min(members, key=rank)
    summary = main.summary or next((m.summary for m in members if m.summary), "")
    hn = max(members, key=lambda m: m.hn_points)
    hf = max(members, key=lambda m: m.upvotes)
    authors = next((m.authors for m in members if m.authors), [])
    others, seen = [], {main.source.lower()}
    for m in sorted(members, key=rank):
        if m.source.lower() in seen or m.feed in ("Hacker News", "HF"):
            continue
        seen.add(m.source.lower())
        others.append({"source": m.source, "link": m.link})
    venue = main.source if d["paper"] else ""
    return {
        "title": main.title, "link": main.link, "source": main.source, "summary": summary,
        "kind": "paper" if d["paper"] else "news", "venue": venue,
        "authors": (", ".join(authors[:3]) + (" 외" if len(authors) > 3 else "")) if authors else "",
        "accepted": next((m.accepted for m in members if m.accepted), ""),
        "org": hf.org if hf.upvotes else "",
        "cats": d["cats"][:2], "score": d["score"], "outlets": d["outlets"],
        "interview": d["interview"], "techmeme": any(m.feed == "Techmeme" for m in members),
        "hn": {"points": hn.hn_points, "comments": hn.hn_comments} if hn.hn_points else None,
        "hf": hf.upvotes or None,
        "published": d["newest"].astimezone(KST).strftime("%m/%d %H:%M"),
        "others": others[:5],
    }


# ---------------------------------------------------------------- 한글 요약
SUMMARY_MODEL = "claude-opus-5-5"
SUMMARY_PROMPT = """아래는 오늘의 IT 뉴스·논문 목록입니다(JSON). 각 항목마다 한국어로 1~2문장(최대 120자) 요약을 써 주세요.
- 주어진 제목·출처·발췌만 근거로 쓰고, 없는 사실을 지어내지 마세요.
- 핵심이 무엇이고 왜 중요한지가 드러나게, 뉴스 브리핑 문체(~했다, ~이다)로 씁니다.
- 회사·제품·모델 이름은 원문 표기를 유지해도 됩니다.
- 모든 id에 대해 하나씩 답하세요.

"""
SUMMARY_SCHEMA = {
    "type": "object",
    "properties": {"items": {"type": "array", "items": {
        "type": "object",
        "properties": {"id": {"type": "integer"}, "summary": {"type": "string"}},
        "required": ["id", "summary"], "additionalProperties": False}}},
    "required": ["items"], "additionalProperties": False,
}


def fetch_meta_description(url: str) -> str:
    """발췌가 없는 기사는 원문 페이지의 og:description 을 가져온다."""
    if "news.google.com" in url:
        return ""
    raw = fetch(url, timeout=12)
    if not raw:
        return ""
    head = raw[:200_000].decode("utf-8", "ignore")
    m = (re.search(r'<meta[^>]+(?:property|name)=["\'](?:og:description|description)["\'][^>]+content=["\']([^"\']+)', head, re.I)
         or re.search(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\'](?:og:description|description)', head, re.I))
    return clip(strip_html(m.group(1)), 300) if m else ""


def summarize_with_claude(rows: list[dict]) -> dict[int, str]:
    import anthropic  # GitHub Actions 에서만 설치되어 있어도 되도록 지연 import

    client = anthropic.Anthropic()
    response = client.beta.messages.create(
        model=SUMMARY_MODEL,
        max_tokens=16000,
        output_config={"effort": "low", "format": {"type": "json_schema", "schema": SUMMARY_SCHEMA}},
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
        messages=[{"role": "user", "content": SUMMARY_PROMPT + json.dumps(rows, ensure_ascii=False)}],
    )
    if response.stop_reason == "refusal":
        raise RuntimeError("요약 요청이 거절되었습니다")
    text = "".join(b.text for b in response.content if b.type == "text")
    return {int(x["id"]): x["summary"].strip() for x in json.loads(text)["items"]}


def translate_fallback(text: str) -> str:
    """API 키가 없을 때: 발췌를 무료 번역(비공식 Google 번역 엔드포인트)으로 한글화."""
    if not text or re.search(r"[가-힣]", text):
        return text
    url = ("https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=ko&dt=t&q="
           + urllib.parse.quote(text[:600]))
    raw = fetch(url, timeout=15)
    if not raw:
        return ""
    try:
        return "".join(seg[0] for seg in json.loads(raw)[0] if seg and seg[0])
    except (ValueError, TypeError, IndexError):
        return ""


def first_sentences(text: str, n: int = 2, limit: int = 140) -> str:
    parts = re.split(r"(?<=[.!?다])\s+", text.strip())
    return clip(" ".join(parts[:n]), limit)


def add_korean_summaries(stories: list[dict]) -> None:
    import os

    with ThreadPoolExecutor(max_workers=8) as ex:
        missing = [s for s in stories if not s["summary"]]
        for s, desc in zip(missing, ex.map(lambda s: fetch_meta_description(s["link"]), missing)):
            s["summary"] = desc
    rows = [{"id": i, "title": s["title"], "source": s["source"], "kind": s["kind"], "snippet": s["summary"]}
            for i, s in enumerate(stories)]
    if os.environ.get("ANTHROPIC_API_KEY"):
        try:
            got = summarize_with_claude(rows)
            for i, s in enumerate(stories):
                s["ko"] = got.get(i, "")
            print(f"한글 요약: Claude로 {sum(1 for s in stories if s['ko'])}/{len(stories)}건")
            return
        except Exception as e:  # noqa: BLE001  요약 실패가 브리핑 전체를 막지 않도록
            print(f"  ! Claude 요약 실패, 번역으로 대체: {e}", file=sys.stderr)
    with ThreadPoolExecutor(max_workers=6) as ex:
        texts = list(ex.map(lambda s: translate_fallback(first_sentences(s["summary"] or s["title"], 2, 400)), stories))
    for s, t in zip(stories, texts):
        s["ko"] = first_sentences(t) if t else ""
    print(f"한글 요약: 번역으로 {sum(1 for s in stories if s['ko'])}/{len(stories)}건")


def render(payload: dict) -> str:
    tpl = (ROOT / "template.html").read_text(encoding="utf-8")
    blob = json.dumps(payload, ensure_ascii=False).replace("</", "<\\/")
    return tpl.replace("/*__DATA__*/null", blob)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--end", help="수집 끝 시각(KST), 예: 2026-11-20T07:00")
    ap.add_argument("--dry", action="store_true", help="파일을 쓰지 않고 결과만 출력")
    args = ap.parse_args()

    t0 = time.time()
    start, end = collection_window(args.end)
    s_k, e_k = start.astimezone(KST), end.astimezone(KST)
    print(f"수집 기간: {s_k:%m/%d %H:%M} ~ {e_k:%m/%d %H:%M} KST")
    items = collect(start, end)
    print(f"기간 내 항목 {len(items)}건")
    clusters = [d for d in select(cluster(items), end)]
    stories_raw, tabs = clusters
    stories = [present(d) for d in stories_raw]
    if not stories:
        print("선정된 기사가 없어 페이지를 갱신하지 않습니다.", file=sys.stderr)
        sys.exit(1)

    for name, ids in tabs.items():
        print(f"\n[{name}] {len(ids)}건")
        for r, i in enumerate(ids, 1):
            s = stories[i]
            tag = "논문" if s["kind"] == "paper" else "뉴스"
            print(f"{r:>3}. [{s['score']:>5}] {tag} {s['title'][:80]} ({s['source']}, {s['outlets']}곳)")
    if args.dry:
        return
    add_korean_summaries(stories)

    now = datetime.now(KST)
    date = e_k.strftime("%Y-%m-%d")
    ARCHIVE.mkdir(exist_ok=True)
    (ARCHIVE / f"{date}.json").write_text(json.dumps({"stories": stories, "tabs": tabs}, ensure_ascii=False, indent=1),
                                          encoding="utf-8")
    dates = sorted({p.stem for p in ARCHIVE.glob("*.html")} | {date}, reverse=True)[:60]
    payload = {"generated": now.strftime("%Y-%m-%d %H:%M"), "date": date, "weekday": "월화수목금토일"[e_k.weekday()],
               "window": f"{s_k:%m/%d %H:%M} ~ {e_k:%m/%d %H:%M}", "stories": stories, "tabs": tabs, "archive": dates}
    page = render(payload)
    (ARCHIVE / f"{date}.html").write_text(page, encoding="utf-8")
    (ROOT / "index.html").write_text(page, encoding="utf-8")
    print(f"\n완료 ({time.time() - t0:.1f}s) -> {ROOT / 'index.html'}")


if __name__ == "__main__":
    main()
