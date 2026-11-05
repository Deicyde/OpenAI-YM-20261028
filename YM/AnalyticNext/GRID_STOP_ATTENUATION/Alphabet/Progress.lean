import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Accounts
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Entry
import YM.Bid.Station
import YM.Work.A15
import YM.Work.B06

set_option warningAsError false

/-! # Uniform price of the repaired presentation, per root response

Volume and number of response inputs arbitrary. The analysis exponent is
bought -> transmitted to every query. Not spending *at each step iterated*;
apply post-Raw BEFORE aggregation internal to one step only. q-valuation
accounts for all moved singleton addresses cumulatively, preserving a
product growth with no factorial allocation. Here: one try.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open RG Marker Wilson Lattice Multi Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V}
variable {G : Gauge} {n : Side} (P : Rep G n)
variable (X : V → Support n)
variable (s : V) (D : Hot R → Pulse G n) (p : Pack n) (z : Site n) (F : Config G n → ℂ) (r : Pack n)

/-- Fee for a constituent exchange entry, including the extra position on
PACK multiplier. -/
structure Costed (δ κ μ w : ℝ) (Y : Support n) : Prop where
  κpos : 0 < κ
  κhi : κ ≤ 1
  rate : 0 ≤ δ
  vacuum : 0 ≤ μ
  anchored : Y ⊆ p.zone
  legal : Legible P.p p F
  stowed : ∃ a : ℝ, 0≤a ∧ (∀ U, ‖F U‖≤a) ∧ (2+μ)*tagCost P (spread p z) δ κ a ≤ w

def covers (y : Hot R) := y.sites.biUnion X

variable {δ κ μ w α σ ρ χ ξ : ℝ}
variable (k : V → ℝ) (H : ∀ i,0<k i)

/-- No Ar-scale burn if the T product itself arrives at reserve needed
here. Don't infer that input costs just because Bulk ultimately came
from a weak 0 exponent at the finer level; at use here needs actual
post response costs e.g. from the analytic gate on THAT level. -/
theorem fire_paid
    (hh : Costed P p z F δ κ μ w (X s))
    (Y : Hot R) (hY : s∈Y.sites) (u : Hot R) (hu : u.sites=Y.sites.erase s)
    (hc : ∀ i,(X i).Nonempty) {m : ℝ}
    (hm : Multi.Credit P.p δ κ (covers X u) (D u) m) :
    Multi.Credit P.p δ κ (covers X Y)
      (-(∑ j∈attaches p z, soloPay (braid p j)
        (shielded P (braid p j) (fun v => F v*(D u).2 j v)))) (w*m) := by
  obtain ⟨hκ,hκ',hd,hμ,hA,hL,a,ha,hf,ha'⟩ := hh
  obtain ⟨-, -, -,hM,-,g,hg,hG⟩ := hm
  have hP : X s ⊆ covers X Y := Finset.subset_biUnion_of_mem X hY
  have hs : (covers X Y).Nonempty := (hc s).mono hP
  have hU : covers X Y = (X s) ∪ covers X u := by unfold covers; rw [hu, ← Finset.biUnion_insert,Finset.insert_erase hY]
  let t := burn P.p δ (spread p z).zone
  have hr : 0 ≤ t := (burn_pos ..).le
  have hH : 0 ≤ tagCost P (spread p z) δ κ a := div_nonneg (mul_nonneg (burn_pos ..).le ha) hκ.le
  have hw : 0 ≤ w := (mul_nonneg (by linarith : 0 ≤ 2+μ) hH).trans ha'
  -- in particular can pay t*a ≤ w (even if κ not small)
  have hz : t * a ≤ w := calc
    _ ≤ (t*a) / κ := le_div_self (mul_nonneg hr ha) hκ hκ'
    _ ≤ (2+μ)*tagCost P (spread p z) δ κ a := le_mul_of_one_le_left hH (by linarith)
    _ ≤ w := ha'
  let E (j : Pack n) (v) := F v*(D u).2 j v
  let f j := soloPay (braid p j) (shielded P (braid p j) (E j))
  let b j := tagCost P (braid p j) δ κ (a*g j)
  have he (j : Pack n) : 0≤ b j := div_nonneg (mul_nonneg (burn_pos ..).le (mul_nonneg ha (hG j).2.2.1)) hκ.le
  have hX j (hi : j∈ attaches p z) : Multi.Credit P.p δ κ (covers X Y) (f j) (b j) := by
    obtain ⟨hW,ho,h0,h1⟩ := hG j
    have hE : UsesFinal P.p.threshold (braid p j).zone (E j) := fun U V hi hl => congrArg₂ (· * ·)
      (final_parent _ (Finset.subset_union_left (s₁:=p.zone) (s₂:=j.zone)) _ hL.reads U V hi hl)
      (final_parent _ (Finset.subset_union_right (s₁:=p.zone) (s₂:=j.zone)) _ hW.reads U V hi hl)
    by_cases he' : (D u).2 j≠0
    · apply solo_credit P (shielded_legible P (hL.borel.mul hW.borel)
        (fun t U => congrArg₂ (·*·) (hL.symmetry ..) (hW.symmetry ..)) hE) hκ (mul_nonneg ha h0) hd
        (guarded P (braid p j) _ (mul_nonneg ha h0) (fun V => (norm_mul_le _ _).trans (mul_le_mul (hf _) (h1 _) (norm_nonneg _) ha)))
        (covers X Y) hs
      rw [hU]; exact union_subset_union hA (ho he')
    have hx : f j=0 := by unfold f E soloPay shielded; simp [not_not.mp he']; funext p U; split <;> rfl
    rw [hx]; exact (Multi.Credit.zero P.p hd hκ hs).expand (he _)
  -- 2+mu in ledger already, don't spend again
  have HB := (Multi.Credit.sums (attaches p z) f b hs hd hκ hX).scale (-1:ℂ)
  rw [neg_one_smul,norm_neg,norm_one,one_mul] at HB
  apply HB.expand
  calc
    _ ≤ ∑ j∈attaches p z,t*a*(burn P.p δ j.zone * g j)/κ := sum_le_sum fun j hi => by
      have hj := (mem_filter.mp hi).2.1
      have ht : coverNumber P.p.B (braid p j).zone ≤ coverNumber P.p.B (spread p z).zone + coverNumber P.p.B j.zone :=
        (Corona.cover_mono (show (braid p j).zone ⊆ (spread p z).zone ∪ j.zone from union_subset_union (Finset.subset_insert ..) subset_rfl) _).trans
          (Corona.meets_sum (x:=z) (show z∈ (spread p z).zone from mem_insert_self ..) hj ..)
      have he' : burn P.p δ (braid p j).zone ≤ t*burn P.p δ j.zone := by
        unfold t burn; rw [←Real.exp_add,←mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast ht)
          (add_nonneg P.p.exponent_pos.le hd))
      refine div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right he' (mul_nonneg ha (hG j).2.2.1)).trans_eq ?_) hκ.le
      ring
    _ ≤ t*a*(κ*m)/κ := by
      rw [←sum_div,←mul_sum]; refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hr ha)) hκ.le
      exact (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => mul_nonneg (burn_pos ..).le (hG i).2.2.1)).trans hg
    _ = t*a*m := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hz hM

-- a small table for the multiplicative toll after editing s only.
def advance (x : V) := if x=s then k s + w else k x 

include H


omit H in
lemma holds_back (x : R.Mode) (h : s ∉ x.val) : Poly.toll (advance s k (w:=w)) x=Poly.toll k x := by
  unfold Poly.toll; exact Finset.prod_congr rfl fun i hi => if_neg (fun (he : i=s) => h (he ▸ hi))

omit H in
lemma toll_renew (x : Hot R) (hx : s∈x.sites) :
    Poly.toll (advance s k (w:=w)) x.val = Poly.toll k x.val + w*Poly.toll k (dim s x.val) := by
  unfold Poly.toll advance dim
  rw [← Finset.mul_prod_erase _ k hx, ← Finset.mul_prod_erase _ _ hx,if_pos rfl]
  change (k s+w)*(∏ i∈x.sites.erase s,_) = _
  rw [Finset.prod_congr rfl (g:=k) (fun i hi => if_neg ((Finset.mem_erase.mp hi).1)),add_mul]

variable (hD : ∀ i,Multi.Credit P.p δ κ (covers X i) (D i) (Poly.toll k i.val))

include hD
omit H in
lemma edit_prices (hc : ∀ i,(X i).Nonempty) (hv : P.Lawful σ ρ χ ξ μ) {μ' : ℝ} (ht : Mint P δ μ')
    (hp : Costed P p z F δ κ μ' w (X s)) (i : Hot R) :
    Multi.Credit P.p δ κ (covers X i) (edited P s D p z F i) (Poly.toll (advance s k (w:=w)) i.val) := by
  by_cases he : s∈i.sites
  · rw [toll_renew s k i he] -- no X
    by_cases hi : i=Hot.one R s
    · subst i
      obtain ⟨hκ,hu,hd,hμ,hh,hA,a,h₁,hH,h₂⟩ := hp
      have hG := kernel_credit P hv ht hκ hd hA h₁ hH (X s) (hc s) hh z
      rw [edited_at,show dim s (Hot.one R s).val=R.quiet from Subtype.ext (by simp [Hot.one,Census.fire,dim,Census.quiet]),Poly.quiet_toll,mul_one]
      apply Multi.Credit.add (hD _) ?_
      unfold covers; rw [Hot.sites_one,singleton_biUnion]
      exact hG.expand h₂
    have hm : (i.sites.erase s).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hi (Hot.eq_of_sites (calc
      _ = insert s _ := (Finset.insert_erase he).symm
      _ = _ := by rw [h,insert_empty_eq]; rfl))
    let u : Hot R := ⟨dim s i.val,hm⟩
    rw [spark _ _ _ _ _ _ i u he rfl,sub_eq_add_neg]
    exact Multi.Credit.add (hD _) (fire_paid P X s D p z F hp i he u rfl hc (hD _))
  rw [dormant _ _ _ _ _ _ i he, holds_back _ _ _ he]; exact hD _
end YM.AnalyticNext.GridStop.Alphabet
