"""Finite incidence computations for the LCTR source survey."""
from collections import Counter, defaultdict, deque
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json

TYPES = ('member', 'dependency', 'branch', 'separate', 'lexical')
AXES = ('order_relation', 'orientation', 'endpoint', 'instant', 'interval_boundary',
        'turning_position', 'transition_position', 'phase_boundary')
TRIPLES = tuple(','.join(map(str, x)) for x in product((0, 1), repeat=3))


def indices(values, domain=None):
    if not isinstance(values, list) or any(type(x) is not int or x < 1 for x in values):
        raise ValueError('An index set must be a list of positive integers')
    if len(values) != len(set(values)):
        raise ValueError('Repeated member in an index set')
    result = set(values)
    if domain is not None and not result <= domain:
        raise ValueError('An index lies outside its declared carrier')
    return result


def closure_scan(seed, transfers, available_claims=None):
    reached = set(seed)
    while True:
        old = reached.copy()
        for edge in transfers:
            if available_claims is not None and not set(edge['claims']) <= available_claims:
                continue
            if set(edge['input_time']) <= reached:
                reached.update(edge['output_time'])
        if old == reached:
            return reached


def closure_queue(seed, transfers, available_claims=None):
    active = [e for e in transfers if available_claims is None or set(e['claims']) <= available_claims]
    remaining = [len(set(e['input_time']) - set(seed)) for e in active]
    watchers = defaultdict(list)
    for i, edge in enumerate(active):
        for node in set(edge['input_time']) - set(seed):
            watchers[node].append(i)
    ready = deque(i for i, n in enumerate(remaining) if n == 0)
    reached = set(seed)
    while ready:
        i = ready.popleft()
        for node in set(active[i]['output_time']) - reached:
            reached.add(node)
            for j in watchers[node]:
                remaining[j] -= 1
                if remaining[j] == 0:
                    ready.append(j)
    return reached


def closure(seed, transfers, available_claims=None):
    scan = closure_scan(seed, transfers, available_claims)
    queue = closure_queue(seed, transfers, available_claims)
    if scan != queue:
        raise ValueError('The two all-input closure algorithms disagree')
    return scan


def binary_closure(nodes, transfers):
    adjacency = {x: set() for x in nodes}
    for edge in transfers:
        for x in edge['input_time']:
            adjacency[x].update(edge['output_time'])
    paths = {}
    for x in nodes:
        seen, pending = set(), list(adjacency[x])
        while pending:
            y = pending.pop()
            if y not in seen:
                seen.add(y)
                pending.extend(adjacency[y] - seen)
        paths[x] = seen
    # A second computation uses bit-matrix transitive closure.
    order = sorted(nodes)
    positions = {x: i for i, x in enumerate(order)}
    matrix = {x: sum(1 << positions[y] for y in adjacency[x]) for x in order}
    for y in order:
        bit = 1 << positions[y]
        for x in order:
            if matrix[x] & bit:
                matrix[x] |= matrix[y]
    if any(paths[x] != {y for y in order if matrix[x] & (1 << positions[y])} for x in order):
        raise ValueError('The two positive-length transitive closures disagree')
    return paths


def compute_source(source):
    times = indices([r['index'] for r in source['time_contents']])
    claims = indices(source['claim_indices'])
    if not times:
        raise ValueError('A survey source must declare time contents')
    transfers = source['transfers']
    transfer_ids = indices([r['index'] for r in transfers])
    result_ids = indices([r['index'] for r in source['results']])
    kinds, axes = {}, {}
    for r in source['time_contents']:
        if r['structural_type'] not in TYPES or not set(r['structural_axes']) <= set(AXES):
            raise ValueError('Unknown structural type or axis')
        if len(r['structural_axes']) != len(set(r['structural_axes'])):
            raise ValueError('Repeated structural axis')
        if (r['structural_type'] == 'member') != bool(r['structural_axes']):
            raise ValueError('Axes are the nonempty memberships of structure members')
        kinds[r['index']], axes[r['index']] = r['structural_type'], r['structural_axes']
    for edge in transfers:
        indices(edge['input_time'], times)
        if not indices(edge['output_time'], times):
            raise ValueError('A time transfer must have a time output')
        indices(edge['claims'], claims)
        indices(edge['input_auxiliary']); indices(edge['output_auxiliary'])
    for result in source['results']:
        indices(result['input_time'], times); indices(result['claims'], claims)
        indices(result['input_auxiliary']); indices(result['admissible_transfers'], transfer_ids)
    projected = closure(set(), transfers)
    initial = source['generation_initial_claim_indices']
    if initial is None:
        if projected:
            raise ValueError('Nonempty temporal projection needs the exact generation initial claim subset')
        generated = set()
        certificate = 'empty_temporal_projection_dominates_every_claim_restricted_closure'
    else:
        generated = closure(set(), transfers, indices(initial, claims))
        if not generated <= projected:
            raise ValueError('Claim restriction violates closure monotonicity')
        certificate = 'temporal_upper_bound_from_declared_generation_initial_claim_subset'
    evidence_results = set()
    branch_cache = {}
    for result in source['results']:
        key = tuple(sorted(result['admissible_transfers']))
        if key not in branch_cache:
            selected = [e for e in transfers if e['index'] in key]
            branch_cache[key] = closure(set(), selected)
        if set(result['input_time']) <= branch_cache[key]:
            evidence_results.add(result['index'])
    paths = binary_closure(times, transfers)
    members = {x for x in times if kinds[x] == 'member'}
    dependencies = {x for x in times if kinds[x] == 'dependency'}
    direct_in = set().union(*(set(e['input_time']) for e in transfers))
    direct_out = set().union(*(set(e['output_time']) for e in transfers))
    result_inputs = set().union(*(set(r['input_time']) for r in source['results']))
    from_members = set().union(*(paths[x] for x in members))
    signatures = {
        'member': {x: (int(x in direct_in), int(x in direct_out), int(x in result_inputs)) for x in members},
        'dependency': {x: (int(bool(paths[x] & members)), int(x in from_members), int(x in result_inputs)) for x in dependencies},
    }
    fibres = {k: {triple: 0 for triple in TRIPLES} for k in signatures}
    for k, values in signatures.items():
        for triple in values.values():
            fibres[k][','.join(map(str, triple))] += 1
    return dict(number=source['number'], reference=source['reference'], time_count=len(times),
                transfer_count=len(transfers), result_count=len(result_ids),
                generation_certificate=certificate, generation_time_upper_bound=sorted(generated),
                generation_zero_certified=not generated,
                primitive_time_certified=sorted(times - generated), locally_reached_time=sorted(projected),
                remaining_after_local=sorted(times - projected),
                evidence_reachable_results_without_supplied_time=sorted(evidence_results),
                root_dependent_results=sorted(result_ids - evidence_results),
                type_counts={k: sum(v == k for v in kinds.values()) for k in TYPES},
                axis_counts={k: sum(k in v for v in axes.values()) for k in AXES},
                signatures={k: {str(x): list(v) for x, v in sorted(rows.items())} for k, rows in signatures.items()},
                signature_fibres=fibres)


def verify(dataset):
    if dataset.get('schema') != 'lctr-survey-incidence/1':
        raise ValueError('Unsupported dataset schema')
    sources = dataset['sources']
    indices([s['number'] for s in sources])
    if len({s['reference'] for s in sources}) != len(sources):
        raise ValueError('Repeated source reference')
    if list(TYPES) != dataset['specification']['time_types'] or list(AXES) != dataset['specification']['structure_axes']:
        raise ValueError('The declared classification schema does not match the computation')
    for s in sources:
        if any(type(x) is not bool for x in s['statement_cohorts'].values()):
            raise ValueError('A cohort membership must be a Boolean')
    rows = [compute_source(s) for s in sources]
    cohorts = {k: [s['number'] for s in sources if s['statement_cohorts'][k]]
               for k in ('time_absence_or_definition_difficulty', 'dynamical_time_program')}
    aggregate = dict(sources=len(rows), time_contents=sum(r['time_count'] for r in rows),
                     transfers=sum(r['transfer_count'] for r in rows), results=sum(r['result_count'] for r in rows),
                     sources_with_primitive_time=sum(bool(r['primitive_time_certified']) for r in rows),
                     sources_with_local_reach=sum(bool(r['locally_reached_time']) for r in rows),
                     locally_reached_time_contents=sum(len(r['locally_reached_time']) for r in rows),
                     completely_generated_time_contents=0 if all(r['generation_zero_certified'] for r in rows) else None,
                     generation_time_upper_bound=sum(len(r['generation_time_upper_bound']) for r in rows),
                     sources_requiring_auxiliary_generation_analysis=[r['number'] for r in rows if not r['generation_zero_certified']],
                     cohort_members=cohorts, type_counts={k: sum(r['type_counts'][k] for r in rows) for k in TYPES},
                     axis_counts={k: sum(r['axis_counts'][k] for r in rows) for k in AXES},
                     signature_fibres={k: {t: sum(r['signature_fibres'][k][t] for r in rows) for t in TRIPLES}
                                       for k in ('member', 'dependency')})
    return dict(status='finite_computations_agree', aggregate=aggregate, sources=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('survey.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = args.input.read_bytes()
    result = verify(json.loads(data))
    result['dataset_sha256'] = hashlib.sha256(data).hexdigest()
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
