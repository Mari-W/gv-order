// A small JSON Schema validator for the keywords schema.json uses. No dependencies.
'use strict';

function validate(schema, data) {
  const errors = [];
  const root = schema;
  const deref = s => {
    while (s && s.$ref) {
      if (!s.$ref.startsWith('#/')) throw new Error('only local $ref: ' + s.$ref);
      const extra = Object.assign({}, s); delete extra.$ref;
      let t = root;
      for (const part of s.$ref.slice(2).split('/')) t = t[part];
      s = Object.keys(extra).length ? Object.assign({}, t, extra) : t;
    }
    return s;
  };
  const type = v => Array.isArray(v) ? 'array' : v === null ? 'null' : Number.isInteger(v) ? 'integer' : typeof v;
  function check(s, v, at) {
    s = deref(s);
    if (s === true || s === undefined) return true;
    if (s === false) { errors.push(`${at}: not allowed`); return false; }
    const before = errors.length;
    if (s.type) {
      const t = type(v);
      const ok = s.type === t || (s.type === 'number' && t === 'integer');
      if (!ok) { errors.push(`${at}: expected ${s.type}, got ${t}`); return false; }
    }
    if ('const' in s && v !== s.const) errors.push(`${at}: must be ${JSON.stringify(s.const)}`);
    if (s.enum && !s.enum.includes(v)) errors.push(`${at}: must be one of ${s.enum.join(', ')}`);
    if (typeof v === 'string') {
      if (s.minLength !== undefined && [...v].length < s.minLength) errors.push(`${at}: shorter than ${s.minLength}`);
      if (s.maxLength !== undefined && [...v].length > s.maxLength) errors.push(`${at}: longer than ${s.maxLength}`);
      if (s.pattern && !new RegExp(s.pattern, 'u').test(v)) errors.push(`${at}: does not match ${s.pattern}`);
    }
    if (typeof v === 'number') {
      if (s.minimum !== undefined && v < s.minimum) errors.push(`${at}: below ${s.minimum}`);
      if (s.maximum !== undefined && v > s.maximum) errors.push(`${at}: above ${s.maximum}`);
    }
    if (Array.isArray(v)) {
      if (s.minItems !== undefined && v.length < s.minItems) errors.push(`${at}: fewer than ${s.minItems} items`);
      if (s.uniqueItems && new Set(v.map(x => JSON.stringify(x))).size !== v.length) errors.push(`${at}: items repeat`);
      const pre = s.prefixItems || [];
      v.forEach((x, i) => { if (i < pre.length) check(pre[i], x, `${at}[${i}]`); else if (s.items !== undefined) check(s.items, x, `${at}[${i}]`); });
    }
    if (v && typeof v === 'object' && !Array.isArray(v)) {
      for (const r of s.required || []) if (!(r in v)) errors.push(`${at}: missing ${r}`);
      for (const [k, x] of Object.entries(v)) {
        const where = `${at}.${k}`;
        if (s.propertyNames) check(s.propertyNames, k, `${at} key ${k}`);
        if (s.properties && k in s.properties) { check(s.properties[k], x, where); continue; }
        const pp = Object.entries(s.patternProperties || {}).find(([p]) => new RegExp(p, 'u').test(k));
        if (pp) { check(pp[1], x, where); continue; }
        if (s.additionalProperties !== undefined) check(s.additionalProperties, x, where);
      }
    }
    if (s.oneOf) {
      const n = s.oneOf.filter(o => { const save = errors.length; check(o, v, at); const ok = errors.length === save; errors.length = save; return ok; }).length;
      if (n !== 1) errors.push(`${at}: matches ${n} alternatives, expected one`);
    }
    return errors.length === before;
  }
  check(schema, data, '$');
  return errors;
}

module.exports = { validate };
