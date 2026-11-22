"""IT 모닝 브리핑: 여러 뉴스 피드를 모아 '주목도'로 순위를 매기고 상위 10개를 HTML로 만든다.

주목도 신호
  - 여러 매체가 같은 이야기를 다루는가 (제목 유사도로 묶어서 매체 수를 셈)
  - Techmeme(업계 편집자가 고른 톱뉴스)에 올랐는가
  - Hacker News 점수
  - Google News가 묶어 보여 주는 관련 기사 수
  - 빅테크 총수 인터뷰/발언 여부, 최신성

표준 라이브러리만 사용한다.  실행:  python fetch_news.py
"""
from __future__ import annotations

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
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "archive"
MAX_ITEMS = 10
WINDOW_HOURS = 36
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PersonalNewsBrief/1.0"
KST = timezone(timedelta(hours=9))

# ---------------------------------------------------------------- 소스
FEEDS = {
    "Techmeme": "https://www.techmeme.com/feed.xml",
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
    "leaders": _gnews("(" + " OR ".join(f'"{n}"' for n in LEADERS[:11]) + ") (interview OR podcast OR keynote) when:1d"),
    "leaders_ko": _gnews("(" + " OR ".join(f'"{n}"' for n in LEADERS_KO) + ") 인터뷰 when:1d", ko=True),
    "transmission": _gnews('("co-packaged optics" OR "optical interconnect" OR 6G OR "subsea cable" OR NVLink OR "silicon photonics" OR "800G" OR "1.6T") when:1d'),
    "robotics": _gnews('(humanoid OR robotaxi OR "physical AI" OR robotics) (Tesla OR Nvidia OR Figure OR Waymo OR Unitree OR "Boston Dynamics" OR Google OR Amazon OR Hyundai) when:1d'),
    "semis_ko": _gnews("(반도체 OR HBM OR 파운드리 OR AI) when:1d", ko=True),
}

# Techmeme 는 편집자 큐레이션이라 가중치가 높다.
SOURCE_WEIGHT = {"Techmeme": 3.0, "SemiAnalysis": 1.5, "IEEE Spectrum": 1.2}

# ---------------------------------------------------------------- 분류
CATEGORIES = {
    "AI": [r"\bai\b", r"artificial intelligence", r"openai", r"anthropic", r"\bclaude\b", r"\bgpt", r"gemini",
           r"\bllms?\b", r"deepmind", r"\bagents?\b", r"chatbot", r"machine learning", r"\bmeta ai\b", r"xai\b",
           r"mistral", r"deepseek", r"인공지능", r"생성형", r"\bAI\b", r"에이전트", r"챗봇", r"거대언어모델"],
    "통신·전송": [r"\b5g\b", r"\b6g\b", r"optic", r"photonic", r"fiber", r"ethernet", r"interconnect", r"serdes",
              r"nvlink", r"ucie", r"\bcpo\b", r"co-packaged", r"telecom", r"subsea", r"undersea cable", r"satellite",
              r"starlink", r"wi-?fi", r"broadband", r"spectrum auction", r"\b800g\b", r"1\.6t", r"infiniband",
              r"통신", r"광모듈", r"광통신", r"네트워크", r"위성", r"전송"],
    "반도체·아키텍처": [r"\bchips?\b", r"\bgpus?\b", r"\bcpus?\b", r"\btpus?\b", r"\bnpu", r"semiconductor", r"tsmc",
                 r"\bhbm", r"\bdram\b", r"\bnand\b", r"risc-v", r"\barm\b", r"x86", r"nvidia", r"\bamd\b", r"intel",
                 r"qualcomm", r"broadcom", r"wafer", r"foundry", r"\b[23]nm\b", r"\b1\.4nm\b", r"packaging",
                 r"blackwell", r"rubin", r"micron", r"asml", r"data ?center", r"supercomputer", r"accelerator",
                 r"반도체", r"칩", r"파운드리", r"메모리", r"삼성전자", r"하이닉스", r"엔비디아", r"데이터센터", r"패키징"],
    "빅테크 리더": [re.escape(n.lower()) for n in LEADERS] + [re.escape(n) for n in LEADERS_KO],
    "로보틱스": [r"robot", r"humanoid", r"autonomous", r"self-driving", r"waymo", r"optimus", r"figure ai",
             r"boston dynamics", r"physical ai", r"drone", r"로봇", r"휴머노이드", r"자율주행", r"피지컬"],
}
CAT_RE = {c: re.compile("|".join(p), re.I) for c, p in CATEGORIES.items()}
# 할인·광고·리뷰성 기사는 제외
JUNK_RE = re.compile(r"deals?|% off|half price|discount|sale|coupon|best .* (to buy|for)|black friday|cyber monday|"
                     r"giveaway|sponsored|특가|할인|이벤트", re.I)
INTERVIEW_RE = re.compile(r"interview|podcast|keynote|says|said|told|remarks|인터뷰|대담|기조연설|밝혔|말했", re.I)

STOP = set("""the a an and or of to in on for with at by from as is are was were be been its it this that
these those into over after about new says said say will can could would should has have had not but
than more most how why what when who which just now up out off amid via vs report reports""".split())


@dataclass
class Item:
    title: str
    link: str
    source: str            # 실제 매체 이름
    feed: str              # 어떤 피드에서 왔는가
    published: datetime
    summary: str = ""
    hn_points: int = 0
    hn_comments: int = 0
    related: int = 0       # Google News 관련 기사 수
    tokens: set = field(default_factory=set)


# ---------------------------------------------------------------- 유틸
def fetch(url: str, timeout: int = 20) -> bytes | None:
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*"})
    for attempt in range(2):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001
            if attempt == 1:
                print(f"  ! {url[:80]} -> {e}", file=sys.stderr)
            time.sleep(1.5)
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
    try:
        d = parsedate_to_datetime(s)
    except Exception:  # noqa: BLE001
        try:
            d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except ValueError:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=KST)
    return d.astimezone(timezone.utc)


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
    t = title.lower()
    words = re.findall(r"[a-z0-9][a-z0-9.\-]+|[가-힣]{2,}", t)
    return {w.strip(".-") for w in words if w not in STOP and len(w.strip(".-")) >= 3 or re.match(r"[가-힣]", w)}


# ---------------------------------------------------------------- 수집
def parse_feed(name: str, raw: bytes) -> list[Item]:
    try:
        root = ET.fromstring(raw)
    except ET.ParseError:
        # 일부 한국 매체는 잘못된 문자를 포함한다
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
        link = child_text(el, "link") or child_text(el, "guid", "id")
        desc_raw = child_text(el, "description", "summary", "encoded", "content")
        pub = parse_date(child_text(el, "pubDate", "published", "updated", "date"))
        if not title or not link or not pub:
            continue
        source, summary, related = name, strip_html(desc_raw), 0
        if name == "Techmeme":
            # 제목 끝의 "(기자/매체)" 를 떼고 원문 링크·매체를 꺼낸다
            m = re.search(r"\(([^()]*)\)\s*$", title)
            if m:
                title = title[: m.start()].strip()
                source = m.group(1).split("/")[-1].strip() or "Techmeme"
            m = re.search(r'<B><A HREF="([^"]+)"', desc_raw, re.I)
            if m:
                link = html.unescape(m.group(1))
            m = re.search(r"&mdash;(?:&nbsp;)?\s*(.*?)</P>", desc_raw, re.S | re.I)
            summary = strip_html(m.group(1)) if m else ""
        elif name.startswith("gnews"):
            m = re.match(r"(.*)\s+-\s+([^-]+)$", title)
            if m:
                title, source = m.group(1).strip(), m.group(2).strip()
            related = max(0, len(re.findall(r"<li", desc_raw, re.I)) - 1)
            summary = ""
        out.append(Item(title=title, link=link, source=source, feed=name, published=pub,
                        summary=clip(summary), related=related, tokens=tokenize(title)))
    return out


def fetch_hn(since: datetime) -> list[Item]:
    ts = int(since.timestamp())
    url = ("https://hn.algolia.com/api/v1/search?tags=story&hitsPerPage=200"
           f"&numericFilters=created_at_i>{ts},points>60")
    raw = fetch(url)
    if not raw:
        return []
    out = []
    for h in json.loads(raw).get("hits", []):
        link = h.get("url") or f"https://news.ycombinator.com/item?id={h['objectID']}"
        dom = urllib.parse.urlparse(link).netloc.replace("www.", "")
        out.append(Item(title=h["title"], link=link, source=dom or "Hacker News", feed="Hacker News",
                        published=datetime.fromtimestamp(h["created_at_i"], timezone.utc),
                        hn_points=h.get("points") or 0, hn_comments=h.get("num_comments") or 0,
                        tokens=tokenize(h["title"])))
    return out


def collect() -> list[Item]:
    since = datetime.now(timezone.utc) - timedelta(hours=WINDOW_HOURS)
    jobs = {**FEEDS, **{f"gnews:{k}": v for k, v in GNEWS.items()}}
    items: list[Item] = []
    with ThreadPoolExecutor(max_workers=10) as ex:
        hn_future = ex.submit(fetch_hn, since)
        results = dict(zip(jobs, ex.map(fetch, jobs.values())))
        for name, raw in results.items():
            got = parse_feed(name, raw) if raw else []
            print(f"  {name:<22} {len(got):>4}")
            items += got
        hn = hn_future.result()
        print(f"  {'Hacker News':<22} {len(hn):>4}")
        items += hn
    now = datetime.now(timezone.utc)
    return [i for i in items if since <= i.published <= now + timedelta(hours=1)]


# ---------------------------------------------------------------- 묶기·점수
def similar(a: set, b: set) -> bool:
    if not a or not b:
        return False
    shared = len(a & b)
    small = min(len(a), len(b))
    return shared >= 5 or (shared >= 3 and shared / small >= 0.4) or (shared >= 2 and shared / small >= 0.67)


def norm_url(u: str) -> str:
    p = urllib.parse.urlparse(u)
    # 쿼리 문자열이 기사 ID인 사이트(articleView.html?idxno=…)가 있어 쿼리도 유지
    q = "&".join(kv for kv in p.query.split("&") if kv and not kv.startswith(("utm_", "oc=", "ref=")))
    return (p.netloc.replace("www.", "") + p.path.rstrip("/") + ("?" + q if q else "")).lower()


def cluster(items: list[Item]) -> list[list[Item]]:
    # 점수가 높을 법한 것부터 대표로 삼는다
    order = sorted(items, key=lambda i: (i.feed != "Techmeme", -i.hn_points, -i.related))
    clusters: list[tuple[set, list[Item]]] = []
    for it in order:
        u = norm_url(it.link)
        for toks, members in clusters:
            # 대표(첫 기사)와만 비교해 연쇄적으로 엉뚱한 기사가 붙지 않게 한다
            same_outlet = it.feed == members[0].feed and not it.feed.startswith("gnews")
            if any(norm_url(m.link) == u for m in members) or (not same_outlet and similar(it.tokens, toks)):
                members.append(it)
                break
        else:
            clusters.append((set(it.tokens), [it]))
    return [m for _, m in clusters]


def categorize(text: str) -> list[str]:
    hits = {c: len(r.findall(text)) for c, r in CAT_RE.items()}
    return [c for c, n in sorted(hits.items(), key=lambda kv: -kv[1]) if n > 0]


def score(members: list[Item]) -> dict:
    now = datetime.now(timezone.utc)
    lead = members[0]
    text = " ".join(f"{m.title} {m.summary}" for m in members[:4])
    cats = categorize(" ".join(m.title for m in members[:6]))  # 분류는 제목 기준
    leader_hit = bool(CAT_RE["빅테크 리더"].search(text))
    interview = leader_hit and bool(INTERVIEW_RE.search(text))
    if interview and "빅테크 리더" in cats:
        cats.remove("빅테크 리더")
        cats.insert(0, "빅테크 리더")

    outlets: dict[str, float] = {}
    for m in members:
        w = SOURCE_WEIGHT.get(m.feed, 1.0)
        if m.feed.startswith("gnews"):
            w = 0.3 + 0.2 * min(m.related, 6)
        if m.feed == "Hacker News":
            w = 0.6 * math.log2(1 + m.hn_points / 25)
        key = m.feed if m.feed in ("Techmeme", "Hacker News") else m.source.lower()
        outlets[key] = max(outlets.get(key, 0), w)
    coverage = sum(sorted(outlets.values(), reverse=True)[:8])
    newest = max(m.published for m in members)
    age_h = (now - newest).total_seconds() / 3600
    recency = 1.5 * max(0.0, 1 - age_h / WINDOW_HOURS)
    s = coverage + recency + (1.5 if interview else 0) + (0.8 if cats else 0)
    return {"score": round(s, 2), "cats": cats, "outlets": len(outlets), "interview": interview,
            "age_h": age_h, "newest": newest}


def pick(clusters: list[list[Item]]) -> list[dict]:
    scored = []
    for members in clusters:
        info = score(members)
        if not info["cats"] or JUNK_RE.search(members[0].title):
            continue  # 관심 분야가 아니면 제외
        scored.append({**info, "members": members})
    scored.sort(key=lambda d: -d["score"])

    chosen, per_cat = [], {}
    min_score = scored[MAX_ITEMS - 1]["score"] * 0.6 if len(scored) >= MAX_ITEMS else 0
    # 1) 분야별 최고 기사 하나씩 (너무 약하면 건너뜀)
    for cat in CATEGORIES:
        for d in scored:
            if d["cats"][0] == cat and d not in chosen and d["score"] >= min_score:
                chosen.append(d)
                per_cat[cat] = per_cat.get(cat, 0) + 1
                break
    # 2) 나머지는 점수순, 한 분야 최대 4개
    for d in scored:
        if len(chosen) >= MAX_ITEMS:
            break
        c = d["cats"][0]
        if d not in chosen and per_cat.get(c, 0) < 4:
            chosen.append(d)
            per_cat[c] = per_cat.get(c, 0) + 1
    chosen.sort(key=lambda d: -d["score"])
    return chosen[:MAX_ITEMS]


# ---------------------------------------------------------------- 출력
def present(d: dict) -> dict:
    members = d["members"]
    pref = ["Techmeme"] + list(FEEDS)  # 원문 링크가 확실한 피드 우선
    def rank(m: Item) -> int:
        return pref.index(m.feed) if m.feed in pref else (50 if m.feed == "Hacker News" else 80)
    main = min(members, key=rank)
    summary = main.summary or next((m.summary for m in members if m.summary), "")
    hn = max(members, key=lambda m: m.hn_points)
    others, seen = [], {main.source.lower()}
    for m in sorted(members, key=rank):
        if m.source.lower() in seen or m.feed == "Hacker News":
            continue
        seen.add(m.source.lower())
        others.append({"source": m.source, "link": m.link})
    return {
        "title": main.title, "link": main.link, "source": main.source, "summary": summary,
        "cats": d["cats"][:2], "score": d["score"], "outlets": d["outlets"],
        "interview": d["interview"], "techmeme": any(m.feed == "Techmeme" for m in members),
        "hn": {"points": hn.hn_points, "comments": hn.hn_comments} if hn.hn_points else None,
        "published": d["newest"].astimezone(KST).strftime("%m/%d %H:%M"),
        "others": others[:5],
    }


def render(stories: list[dict], generated: datetime, archive_dates: list[str]) -> str:
    tpl = (ROOT / "template.html").read_text(encoding="utf-8")
    data = {"generated": generated.strftime("%Y-%m-%d %H:%M"), "date": generated.strftime("%Y-%m-%d"),
            "weekday": "월화수목금토일"[generated.weekday()], "stories": stories, "archive": archive_dates}
    blob = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    return tpl.replace("/*__DATA__*/null", blob)


def main() -> None:
    t0 = time.time()
    print("수집 중…")
    items = collect()
    print(f"최근 {WINDOW_HOURS}시간 기사 {len(items)}건")
    stories = [present(d) for d in pick(cluster(items))]
    if not stories:
        print("선정된 기사가 없어 페이지를 갱신하지 않습니다.", file=sys.stderr)
        sys.exit(1)
    now = datetime.now(KST)
    ARCHIVE.mkdir(exist_ok=True)
    (ARCHIVE / f"{now:%Y-%m-%d}.json").write_text(json.dumps(stories, ensure_ascii=False, indent=1), encoding="utf-8")
    dates = sorted((p.stem for p in ARCHIVE.glob("*.json")), reverse=True)[:30]
    (ARCHIVE / f"{now:%Y-%m-%d}.html").write_text(render(stories, now, dates), encoding="utf-8")
    (ROOT / "index.html").write_text(render(stories, now, dates), encoding="utf-8")
    for i, s in enumerate(stories, 1):
        print(f"{i:>2}. [{s['score']:>5}] {'/'.join(s['cats'])}: {s['title'][:90]} ({s['source']}, {s['outlets']}곳)")
    print(f"완료 ({time.time() - t0:.1f}s) -> {ROOT / 'index.html'}")


if __name__ == "__main__":
    main()
