-- rumur_flags: ['--smt-simplification', 'on'] + smt_args() + ['--smt-logic', 'AUFBV', '--smt-bitvectors', 'on']
-- skip_reason: 'no SMT solver available' if len(smt_args()) == 0 else None

-- test that the SMT bridge can cope with negation when using a bitvector logic

var
  x: 8 .. 9;
  y: boolean;

startstate begin
  y := true;
end;

rule begin
  -- the following condition should be simplified to `true` avoiding a read of
  -- `x` when it is undefined
  if -x = -8 | -x = -9 then
    y := !y;
  end;
end;
