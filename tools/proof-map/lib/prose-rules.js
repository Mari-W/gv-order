// Default prose rules. Each rule sees the text with $math$ and `code` replaced by X.
// A map's check extension may add rules (proseRules) or switch some off by name (disableProse).
'use strict';

const rules = [
  // punctuation
  { name: 'semicolon', re: /;/g, why: 'Split into two sentences.' },
  { name: 'colon', re: /:(?=\s)/g, why: 'Split into two sentences or restructure.' },
  { name: 'em dash', re: /[—–]|\s--\s/g, why: 'Use a period, a comma or parentheses.' },
  // words and phrases
  { name: 'since', re: /\bsince\b/gi, why: 'Write because, or restructure.' },
  { name: 'filler word', re: /\b(novel|significant|comprehensive|robust|substantial|seamless|crucial(ly)?|pivotal|delve|leverage|underscore|testament|landscape|realm|notably|essentially|simply|indeed|moreover)\b/gi, why: 'Cut it or name the specific thing.' },
  { name: 'hedge', re: /\b(might|perhaps|possibly|arguably|somewhat|seems?|presumably|likely)\b/gi, why: 'State what is the case.' },
  { name: 'throat-clearing', re: /\b(it is (important|worth) (to note|noting)|in order to|note that)\b/gi, why: 'Cut it.' },
  { name: 'metaphor', re: /\b(costs?|paid|pays?|price|cheap|for free|in return|budget|spend|spends|spent|lives? in|rests? on|reach(es)?|sits?|lands? in|stands? at|talks?|tells?|knows?|sees?|answers?|promises?|behaves?|carries|carry|travels?|hands? (over|on)|owes?|thus|just)\b/gi, why: 'Say what the definition does, without a picture.' },
  { name: 'like', re: /\b[Ll]ike\b(?! to)/g, why: 'Write "such as" or name the case.' },
  { name: 'pronoun ending', re: /\b(it|them)\.(\s|$)/g, why: 'End on the noun that carries the weight.' },
  { name: 'every/any/all', re: /\b(every|any|all)\b/gi, why: 'Quantify only where the definition quantifies.' },
  { name: 'not X but', re: /\bnot\b[^.]{0,40}\bbut\b|, not\b/gi, why: 'State the positive claim.' },
  { name: 'this/here opener', re: /(^|\.\s)(This (section|block)|Here|We now|In this section)\b/g, why: 'Lead with the claim.' }
];

const MAX_WORDS = 35;

// $..$ and `..` become X, mode markers disappear but keep their text
function plain(t) {
  return String(t)
    .replace(/\\inmode(?:plain)?\{[^}]*\}\{/g, '')
    .replace(/\$[^$]*\$/g, 'X')
    .replace(/`[^`]*`/g, 'X')
    .replace(/\[\[[^\]|]*\|([^\]]*)\]\]/g, '$1')
    .replace(/\[\[[^\]]*\]\]/g, 'X');
}

function lint(text, active) {
  const p = plain(text), hits = [];
  for (const r of active) {
    const re = new RegExp(r.re.source, r.re.flags.includes('g') ? r.re.flags : r.re.flags + 'g');
    for (const m of p.matchAll(re)) hits.push({ rule: r.name, match: m[0].trim(), why: r.why, severity: r.severity || 'warning' });
  }
  for (const s of p.split(/(?<=[.?!])\s+(?=[A-Z$X])/)) {
    const n = s.split(/\s+/).filter(Boolean).length;
    if (n > MAX_WORDS) hits.push({ rule: 'sentence > ' + MAX_WORDS + ' words', match: s.slice(0, 60) + '…', why: n + ' words. Split it.', severity: 'warning' });
  }
  return hits;
}

module.exports = { rules, lint, plain, MAX_WORDS };
