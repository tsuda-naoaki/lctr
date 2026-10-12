/* Copyright 2026 Naoaki Tsuda. SPDX-License-Identifier: BSD-3-Clause */
const {test} = require('node:test');
const assert = require('node:assert/strict');
const {evaluate} = require('../site/assets/create-time.js');

test('both coordinate choices preserve and reflect every ordered pair', () => {
  for (const spacing of ['even','uneven']) {
    const {reach, coordinates} = evaluate('complete', spacing);
    assert.ok(coordinates);
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
      assert.equal(coordinates[i] < coordinates[j], reach[i][j]);
      assert.equal(coordinates[i] === coordinates[j], i === j);
    }
  }
  assert.deepEqual(evaluate('complete','even').coordinates,[0,1,2]);
  assert.deepEqual(evaluate('complete','uneven').coordinates,[0,1,4]);
});
test('non-transitive incomparability is not silently forced into a total order', () => {
  for (const spacing of ['even','uneven']) {
    const r = evaluate('incomplete',spacing);
    assert.equal(r.acyclic,true);
    assert.equal(r.reach[0][1],true);
    assert.equal(r.reach[0][2] || r.reach[2][0],false);
    assert.equal(r.reach[2][1] || r.reach[1][2],false);
    assert.equal(r.total,false);
    assert.equal(r.coordinates,null);
  }
});
test('the cycle produces reflexive reach and no numerical representation', () => {
  const r = evaluate('cycle');
  assert.equal(r.acyclic,false);
  assert.ok(r.reach.every((row,i) => row[i]));
  assert.equal(r.coordinates,null);
});
test('invalid inputs fail explicitly; calls do not retain earlier results', () => {
  assert.throws(() => evaluate('unknown'));
  assert.throws(() => evaluate('complete','seconds'));
  const before = evaluate('complete');
  evaluate('cycle');
  assert.deepEqual(evaluate('complete'),before);
});
