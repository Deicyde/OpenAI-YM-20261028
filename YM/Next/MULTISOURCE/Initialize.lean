import YM.Next.MULTISOURCE.Accrue
import YM.Next.MULTISOURCE.Birth

/-!
# Startup, rooted and first response receipts
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi

open RG Wilson Lattice Function Finset Marker Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side}
variable (P : Rep G n)

private def test : Census Unit where
  choices := univ
  solo := by simp
  blank := by simp
  down := by simp

lemma birth_tangent (C : Vessel G n) {δ w : ℝ} (hp : P.activities.Valid P.p δ w)
    (h : Couples.Weight P.p C.siteSet (C.tail P)) (U : Config G n) :
    tangent P (C.birth P) U=(P.eval U:ℂ)*C.full U := by
  let F := fun _ : Unit => C
  have he : tangent P (C.birth P) U=_ := (congrArg (fun D => tangent P D U) (birth_copy P F test ()).symm)
  rw [he, ← firstMany P hp _ () U, first_prepare P F hp (fun _ => h)]
  change _*(∏ i ∈ {()}, _)=_
  rw [prod_singleton]

lemma Credit.soft {P : BudgetPoint} {r c κ : ℝ} {o : Support n} {D : Pulse G n} (H : Credit P r κ o D c) :
    Credit P 0 κ o D c := by
  obtain ⟨hx,hr,hk,hc,⟨i,F,hi,hH,hy,hF⟩,p,hp,H⟩ := H
  have he : fare P r o ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (by positivity))
  refine ⟨hx,le_rfl,hk,hc,⟨i,F,hi,hH,hy,(hF.rebate hr).enlarge (mul_le_of_le_one_left hc he)⟩,
    p, le_trans (Finset.sum_le_sum fun v _ => ?_) hp,H⟩
  refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (H v).2.2.1
  gcongr



variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

lemma startups (C : V → Vessel G n) (R : Census V) (o : V → Site n) {κ w : ℝ} {p b : V → ℝ} {m : ℕ}
    (h : ∀ i,(C i).Check P (o i) m (b i) (p i)) {δ v : ℝ} (H : P.activities.Valid P.p δ v)
    (hK : 0 < κ) (hk : κ ≤ 1) (hp : Mint P 2 κ) (ho : Spaced o P.p.B) (hv : Spot P.p)
    (hw : 0 < w) (ht : ∀ i,w*p i ≤ 1/8) :
    ∃ g : Hot R → ℝ,(∀ i,g (Hot.one R i)=p i) ∧ Afield P.p κ o (prepare P R C) g w := by
  let g (x : Hot R) := fare P.p 2 (x.sites.image o)*(∏ i∈x.sites,p i)
  have he i := seed_credit P C R o i h H hK hk hp
  refine Afield.balance P.p κ o _ w p g (fun i => by simpa only [Hot.sites_one,image_singleton,prod_singleton]
    using (he (Hot.one R i)).soft) ht ?_ ?_
  · intro x hx; refine (he x).refund (by rwa [card_image_of_injective _ (ho.injective P.p.B_pos)])
  intro i
  refine le_trans (sum_le_sum (g:=fun x : Hot R => fare P.p 1 (x.sites.image o)) (fun j hj => ?_))
    (root_campaign R i P.p ho hv)
  have hf : (∏ i∈j.sites,(w*p i)) ≤ 1 := prod_le_one (fun v _ => mul_nonneg hw.le ((norm_nonneg _).trans (h v).paid))
    fun v _ => (ht v).trans (by norm_num)
  rw [prod_mul_distrib,prod_const] at hf
  unfold current g
  rw [mul_left_comm]
  apply (mul_le_of_le_one_right (Real.exp_pos _).le hf).trans
  apply Real.exp_monotone; nlinarith only [(show (0:ℝ) ≤ coverNumber P.p.B (j.sites.image o) by positivity)]
end YM.Multi
