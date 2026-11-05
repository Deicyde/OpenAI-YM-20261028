import YM.RG08.Crown.Towers

/-! # Final top formal normalized branch; powers rescaled. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset Filter Lattice Rudder Forms Pert.Bulk
open Wilson WilsonStartup Design Exterior Anchor Rudder.Symmetry RG Loop
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace
variable {G:YM.Gauge}{P:Side}{n:ℕ}

def turns (s:Signed):Cellar (Bedge G P)→L[ℝ] Cellar (Bedge G P):=
 ContinuousLinearMap.pi fun i=>supply s i.2 • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bedge G P=>ℝ) (badge s i)
lemma turns_affine (s:Signed)(v:Cellar (Bedge G P)):turns s v=treated s v:=rfl
lemma switch {f:Still (Bedge G P)}(h:Camera.Pace f)(s:Signed)(k:ℕ)(v:Cellar (Bedge G P)):
 MvPolynomial.eval (treated s v) (tap k (flask f))=MvPolynomial.eval v (tap k (flask (f ∘ turns s))):=by
 rw [glimpses h,glimpses (show Camera.Pace (f ∘ turns s) from ContDiffAt.comp 0 (by rw [map_zero];exact h) (turns s).contDiff.contDiffAt), Next.Foundations.jets_linear (turns s) (show ContDiffAt ℝ k f 0 from h.of_le le_top)]
 rfl

def gold (G:YM.Gauge)(P:Side):Port (Bedge G P):= flask (energy ∘ offers G (P:=P))
lemma gold_ore (G:YM.Gauge)(P:Side)(k K:ℕ)(h:k≤K):tap k (gold G P)=∑ i∈Finset.range (K+1),if i=0∨Odd i then 0 else ∑ p:PlaqAxes,∑ x:Site P,tap k (flask (sheet G x p i)):=by
 let f(x : Site P)(i:PlaqAxes):Still (Bedge G P):= fun y=>G.price (faceValue (offers G y) (x,i))
 have he(p):Camera.Pace (∑ i,f p i):=by simpa only [←Finset.sum_apply] using (ContDiffAt.sum (s:=univ) (f:=f p) (fun i _=>power _ _ _))
 have ha : energy ∘ offers G (P:=P)=∑ p,∑ i,f p i:=by funext y; unfold energy;simp [Finset.sum_apply,Fintype.sum_prod_type,f]
 rw [gold,ha,slurry _ _ (fun p _=>he p)];simp_rw [slurry _ _ (fun (i:PlaqAxes) _ => show Camera.Pace (f _ i) from power G _ i)]
 unfold tap;rw [map_sum];simp_rw [map_sum,←show ∀ v:Port (Bedge G P),tap k v=PowerSeries.coeff k v from fun _=>rfl, f, march _ _ K k h]
 -- swap sums three
 rw [show (∑ x:Site P,_)=(∑ i∈range (K+1),∑ p:PlaqAxes,∑ x:Site P,if i=0∨ Odd i then (0:Inn (Bedge G P)) else tap k (flask (sheet G x p i))) from ?_];apply Finset.sum_congr rfl;intro i _;split <;> simp [*]
 rw [Finset.sum_comm];apply Eq.trans (Finset.sum_congr rfl fun _ _=> Finset.sum_comm);rw [Finset.sum_comm]

lemma gold_const (G:YM.Gauge)(P:Side):Low 2 (gold G P):=by intro i hi;rw [gold_ore _ _ _ _ le_rfl];interval_cases i <;>norm_num [Finset.sum_range_succ,Nat.odd_iff]

def groupUse (k n:ℕ)(i:Fin n)(v:Cmix P G.ColorIndex 1→ℝ):ℝ:= if hk:k=0∨Odd k then 0 else carduse G k n ⟨0,Nat.pos_of_ne_zero (fun h=>hk (Or.inl h))⟩ i v
-- `gold` already receives e≥0 via divided operation. Reading on any regulator P,
-- read finite only through n. k-branch has input action g^-2 unrescaled,
-- leading slots g^k. Thus packet contributes starting at k-2. base is k=2.
def recitation (G:YM.Gauge)(n:ℕ):Flake (n+2) (Market (Rayk G 1)):=∑ k∈range (n+3), if hk:k=0∨Odd k then 0 else Carrel.completed (prize G k) ⟨0,Nat.pos_of_ne_zero (fun h=>hk (Or.inl h))⟩ (n+2)

theorem rings (G:YM.Gauge)(P:Side)(n:ℕ)(o:Fin (n+2))(v:Cmix P G.ColorIndex 1→ℝ):
 MvPolynomial.eval v (tap n (tax 2 (gold G P)))=(∑ k∈range (n+3),groupUse k (n+2) o v):=by
 have hp: Camera.Pace (energy ∘ offers G (P:=P)):=by
    unfold energy
    exact ContDiffAt.sum (fun p _=>power G p.1 p.2)
 rw [audited]
 let K:=range (n+3)
 let r:=(Fintype.card Signed:ℝ)
 have hr:r≠0:=by unfold r;exact_mod_cast Fintype.card_ne_zero
 let Q (s:Signed)(i):= if i=0∨ Odd i then 0 else ∑ p:PlaqAxes,∑ y:Site P,MvPolynomial.eval (treated s v) (tap (n+2) (flask (sheet G y p i)))
 have H(s:Signed):MvPolynomial.eval v (tap (n+2) (gold G P))=∑ i∈K,Q s i:=by
   have he: MvPolynomial.eval (treated s v) (tap (n+2) (gold G P))=MvPolynomial.eval v (tap (n+2) (gold G P)):=by
      unfold gold;rw [switch hp]
      have ht: (energy ∘ offers G (P:=P)) ∘ turns s=energy ∘ offers G (P:=P):=by funext i; simp [comp_def,turns_affine,tread,energy_pull]
      rw [ht]
   rw [←he,gold_ore G P _ (n+2) le_rfl,map_sum];apply Finset.sum_congr rfl;intro i _; unfold Q;split <;> simp [*,map_sum]
 calc
  _ = r⁻¹*(∑ s:Signed,∑ i∈K,Q s i) :=by simp_rw [←H];rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hr]
  _ = _:=by rw [Finset.sum_comm,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;unfold groupUse Q;split <;> first|simp [*]|skip -- matinee maybe simp
            rw [matinee]
end YM.RG08.Crown
