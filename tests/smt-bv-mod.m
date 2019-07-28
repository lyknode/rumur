-- rumur_flags: ['--smt-simplification', 'on'] + smt_args() + ['--smt-logic', 'QF_BV']
-- skip_reason: 'no SMT solver available' if len(smt_args()) == 0 else None

-- test that the SMT bridge can cope with modulo when using a bitvector logic

var
  x: 8 .. 9;
  y: boolean;

startstate begin
  y := true;
end;

rule begin
  -- the following condition should be simplified to `true` avoiding a read of
  -- `x` when it is undefined
  if x % 5 = 3 | x % 5 = 4 then
    y := !y;
  end;
end;