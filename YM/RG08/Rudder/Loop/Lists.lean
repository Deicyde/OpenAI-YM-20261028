import YM.RG08.Rudder.Pier

/-!
# Rank two moment argument on position stencils. All on cover. Keeps exact orientation.
-/
noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- zero and secondary slot -/
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
abbrev ProductR := ArrayC (Fin 2) ℤ ℝ
abbrev Flag:=Finset Axis
abbrev place(x: Cover × Flag)(y:Cover × Flag):Fin 2→Cover × Flag:=Fin.cons x (fun _=>y)
lemma place_o (x y : Cover × Flag):place x y o=x:=rfl
lemma place_p (x y:Cover × Flag):place x y p=y:=rfl

/-- columns always anchored in first location -/
def col (A:ProductR)(i j:Flag)(v:Cover):=A (place (0,i) (v,j))
lemma prices {A:ProductR}(h:Cohere A)(x y : Cover × Flag) : A (place x y)=col A x.2 y.2 (y.1-x.1):=by
 rw [←h (-x.1)];unfold col;congr 1;ext k:1; cases k using Fin.cases with
 | zero=> simp [place,move]
 | succ k=>simp [place,move,sub_eq_add_neg]

lemma price_place {A:ProductR}(h:Cohere A)(z:Fin 2→Cover × Flag): A z=col A (z o).2 (z p).2 ((z p).1-(z o).1):=by
 have he:z=place (z o) (z p):=by funext i; cases i using Fin.cases with
 | zero=>rfl
 | succ i=>rw [Subsingleton.elim i (0:Fin 1)];rfl
 rw [←prices h];exact congr_arg _ he

lemma edit_o(i:Cover × Flag)(z:Fin 2→Cover × Flag): update z o i=place i (z p):=by funext j;cases j using Fin.cases with
 | zero=>simp [place]
 | succ j=> rw [Subsingleton.elim j (0:Fin 1),update_of_ne (Fin.succ_ne_zero _)];rfl
lemma edit_p(i:Cover × Flag)(z:Fin 2→Cover × Flag): update z p i=place (z o) i:=by funext j;cases j using Fin.cases with
 | zero=>rw [update_of_ne (Ne.symm (Fin.succ_ne_zero (n:=1) _))];rfl
 | succ j=>rw [Subsingleton.elim j (0:Fin 1),update_self];rfl

lemma rim_secondary {A:ProductR}(_h:Cohere A)(i j:Flag)(v:Cover):col (lower p A) i j v=∑ a,if a∈j then 0 else sign j a * (col A i (insert a j) (v-step a)-col A i (insert a j) v):=by
 unfold col;rw [lower_at];apply sum_congr rfl;intro k _
 rw [sect_at,place_p];split_ifs; · rfl
 unfold peek;rw [edit_p,edit_p];rfl
lemma rim_primary {A:ProductR}(h:Cohere A)(i j:Flag)(v:Cover):col (lower o A) i j v=∑ a,if a∈i then 0 else sign i a * (col A (insert a i) j (v+step a)-col A (insert a i) j v):=by
 unfold col;rw [lower_at];apply sum_congr rfl;intro k _
 rw [sect_at,place_o];split_ifs; · rfl
 unfold peek;rw [edit_o, edit_o,place_p,prices h (0-step k,insert k i)]; simp [col]

def first (f:Cover→ℝ)(i:Axis):=∑' v: Cover,(v i:ℝ)*f v
def load (f:Cover→ℝ):=∑' v,f v

def Moment (f:Cover→ℝ) : Prop := Summable f ∧ ∀ i:Axis,Summable fun v=> (v i:ℝ)*f v

lemma fee (i:Axis)(v:Cover): |(v i:ℝ)|≤length v:=by
 have he:(v i).natAbs≤ size v:= Finset.single_le_sum (f:=fun i=> (v i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i)
 rw [← Int.cast_abs, Int.abs_eq_natAbs,Int.cast_natCast]; exact_mod_cast he

lemma col_pay {A:ProductR}{σ C:ℝ}(h:Pricing A σ C)(i j:Flag): Moment (col A i j):=by
 have H(v:Cover):|col A i j v| ≤ C*Real.exp (-σ*size v):=by -- not imported Isles.Shores? Pier not
   simpa only [Real.norm_eq_abs,cost,sub_zero, col,place_o,place_p] using h.each (place (0,i) (v,j)) p o
 have hp:=h.rate;have hc:=h.cap
 let u:=σ/2;have hu:0<u:=half_pos hp
 let e (v:Cover):=Real.exp (-u * size v)
 have hh:Summable e := (Width.compactPay u hu).2.1
 have he(v:Cover):Real.exp (-σ * size v)=e v*e v:=by unfold e u; rw [←Real.exp_add]; congr 1;ring
 refine ⟨Summable.of_norm_bounded (hh.mul_left C) (fun v=>?_),fun k=> Summable.of_norm_bounded (hh.mul_left (C/u)) fun v=> ?_⟩
 · rw [Real.norm_eq_abs]; refine (H v).trans ?_; unfold e u;gcongr;linarith
 rw [Real.norm_eq_abs,abs_mul]
 specialize H v;rw [he] at H
 apply (mul_le_mul (fee k v) H (abs_nonneg _) (by unfold length;positivity)).trans
 have hz:length v*e v≤1/u:=by
    unfold e;rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,div_le_div_iff₀ (Real.exp_pos _) hu]
    simpa only [mul_comm (length v) u,one_mul] using ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (u*length v)))
 calc
 _ = (length v*e v)*(C*e v):= by ring
 _ ≤ (1/u)*(C*e v):=mul_le_mul_of_nonneg_right hz (mul_nonneg hc (Real.exp_pos _).le)
 _ = _:=by ring

end YM.RG08.Rudder.Loop
