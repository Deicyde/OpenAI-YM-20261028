import YM.MergeProof.West.Longbow
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition Filter
-- support and growth assembled
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points n}{A : Levels G} {R:Lead G A.S p} {c:Course C N p k}{P:Purse}{s:ℝ}{Ψ : AtlasData G A.S p}

structure Kith (F : Fin n → poly (Chamber G A.S k p)) (x:Points n) (P:Purse) : Prop where
   limit (i:Fin n) : coin (F i) ≤ P.principal (clim A k)
   sound i : totalDegree (F i) ≤ P.taylor
   lofty i : Poetic (F i)
   regions i : ∀ u∈ (F i).vars,fog A x P.band p 8 (walls (clim A k)) le_rfl i u

variable {F : Fin n → poly (Chamber G A.S k p)} (hv:Kith (A:=A) F x P)
local notation "t"=> clim A k
local notation "G'"=> P.principal t
include hv
lemma works (v : modes (Fin n)) : let X:= ∏ i ∈ v.val, F i; coin X ≤ G'^n ∧ totalDegree X ≤ n*P.taylor := by
    intro X
    have hx : v.val.card ≤ n:= (Finset.card_le_univ ..).trans (by simp)
    refine ⟨?_,?_⟩
    · rw [show X=(v.val.toList.map F).prod from (Finset.prod_map_toList ..).symm]
      apply (coins_list _ _ _ (Real.exp_pos _).le hv.limit).trans (pow_le_pow_right₀ (principal_ge P _) ?_); simpa using hx
    rw [show X=(v.val.toList.map F).prod from (Finset.prod_map_toList ..).symm]; refine (degree_list _ _ _ hv.sound).trans ?_; rw [length_toList];gcongr
variable (hq:Caff (G:=G) P (clim A k) (k-middle A P.band k) u n)
include hq
lemma metopia (hi : middle A P.band k ≤ j) (hk : j≤k) (hm:∀ u, j≤u→ u<k→ (R u).Fair P.L)(v:modes (Fin n)): coin (heads R F hk v)≤rentFt P t n ∧ totalDegree (heads R F hk v)≤ degrFt P n:= by
  obtain ⟨ht,hV⟩:= works hv v; obtain ⟨h,hg⟩:= flying R _ hk P.loan hm hV
  have he:hike P.L (n*P.taylor) (k-j)≤knox t := le_trans (pow_le_pow_right₀ (pay_crest P.loan _) (Nat.sub_le_sub_left hi k)) hq.hikes
  exact ⟨h.trans (mul_le_mul ht he (ample P.L _ _ P.loan) (pow_nonneg (Real.exp_pos _).le _)),hg.trans (deg_best ..)⟩

lemma topica (hi : middle A P.band k ≤ j) (hk : j≤k) (hm:∀ u, j≤u→ u<k→ (R u).Fair P.L)(v:modes (Fin n)): coin (vista R F hk v)≤ quotaFt P t n ∧ totalDegree (vista R F hk v)≤ degrFt P n:= by
  refine ⟨(coinCost _ _ _ (zero_le_one.trans (rent_buy ..)) (fun i=>(metopia hv hq hi hk hm i).1)).trans (quota_cost ..),?_⟩
  exact (degreeCost _ _ _ (fun i=>(flying R _ hk P.loan hm (works hv i).2).2)).trans (deg_cost ..)

lemma housing (h : middle A P.band k ≤ j) (hi:j≤k) (X : ReadySh (A:=A) P.band Ψ P.horizon P.era.coast.Q k R) (v:Manner n) :
   (vista R F hi v.val ≠ 0 → cosy A x P.band p P.horizon (walls (clim A j)) hi v) ∧
   ∀ i∈(vista R F hi v.val).vars, fog A x P.band p (P.horizon+8) (walls (clim A j)) hi (Head v) i:=by
   let V:= v.val.val; let B:=walls (clim A j); let y:= P.horizon*B
   have hp : vista R F hi v.val ≠0→ cosy A x P.band p P.horizon (walls (clim A j)) hi v:= by
      intro hV; apply Classical.byContradiction; intro h'
      apply hV (a_schism R F hi h X.canvas X.withers hv.regions ?_ v h'); have ht:= (hq.horizon).trans (Nat.div_le_self ..); omega
   refine ⟨hp,fun i he=> ?_⟩
   obtain ⟨-,j,hj,hV⟩:= mem_filter.mp (emigrates hi R F h X.canvas X.withers hv.regions v.val he)
   have hf:= hp (fun ht=> (by rw [ht] at he; simp at he))
   exact (separation_triangle ..).trans ((add_le_add (hf _ (head_member v) j hj) hV).trans_eq (add_mul ..).symm)

-- typing R/X path in output via A. choose name in C path.
omit hv hq
variable {R:Lead G C.S p}{F:Fin n→poly (Chamber G C.S k p)} (hv:Kith (A:=C.path.levels) F x P)
    (hq:Caff (G:=G) P (clim C.path.levels k) (k-middle C.path.levels P.band k) u n) {Ψ : AtlasData G C.S p}
def tapestry (hk:i ≤ k) (hi:middle C.path.levels P.band k≤ i) (X:ReadySh (A:=C.path.levels) P.band Ψ P.horizon P.era.coast.Q k R) (c:Course C N p k) (v:Bale C k P.band p P.horizon x hk):=mimicFt x P.band p c.allow hk hi X.canvas v (vista R F hk v.2.val.val) (anneals C c i)
   (housing hv hq hi hk X v.2.val).2 (woven _ F hk (fun u hu=> X.gauge u (hi.trans hu)) hv.lofty _)

end YM.Next.Rank.Tapes.West
