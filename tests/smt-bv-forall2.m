-- rumur_flags: self.config['SMT_BV_ARGS']
-- skip_reason: 'no SMT solver available' if self.config['SMT_BV_ARGS'] is None else None

-- equivalent of smt-forall2.m but using --smt-bitvectors on

type
  t: 1 .. 2;

var
  x: boolean;
  y: boolean;

startstate begin
  x := true;
end;

rule begin
  -- if the SMT bridge is working correctly, it should simplify the condition as
  -- a tautology into true, avoiding the read of an undefined variable
  if y | forall z: t do z = 1 | z = 2 end then
    x := !x;
  end;
end;
