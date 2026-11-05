import YM.WilsonBulk.Cash.Lighthouse

/-!
# Cancellation on tree line from pre-iteration accuracy

At Leading B covariance predictor on ABSOLUTE free-rooted tree, pressure to cross curvature estimate
without carrying lift; rank-k uses ALL Ψ colors orth frame. Strict gauge move line is NOT paid at rank-e
recurrent: `pulse_cost` buys earlier grade. No assumption that shaft preserves lower degree separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {f c L : Side} {α β : Type} {n : ℕ} {P : Patch} {B Q : Bed} {K : KernelChoices} {S : StepData c f}
variable {σ θ A C η M ε : ℝ}

-- pickup induces same density Jacobian; replicate F row regardless of reading alias
abbrev Pace (L : Side) (G : Gauge) := Cross L (Cloth G) (Cloth G)
def perched (V : Cross L (Loc G 0) α) : Cross L (Cloth G) α := fun i j=> V (i.1,sleeve G i.2) j
lemma perch_cost {V : Cross L (Loc G 0) α} (h : V.strip σ M) : (perched V).strip σ M:=fun _ _=> h _ _
lemma perch_planted (F : Cross S.ratio.count (Loc G 0) α) (x : Pennant G f) (j : Co c α) : installed S.ratio (perched F) x j = installed S.ratio F (x.1,sleeve G x.2) j := rfl
lemma perched_matters (F : Cross S.ratio.count (Loc G 0) α) :
    (turmoil G).acts f * installed S.ratio (perched F) = patron G (Exterior.d 0 f)* installed S.ratio F := by
  -- no α multiplicity
  ext i j; simp only [Matrix.mul_apply,Fintype.sum_prod_type, turmoil_spurs]
  refine sum_congr rfl fun k _=> ?_; simp only [perch_planted,ite_mul,zero_mul]; rw [sum_comm,sum_comm (s:=(univ:Finset (TypeFace 0)))]; refine sum_congr rfl fun u _=>?_ ; simp only [sum_ite_eq', mem_univ, if_true,sleeve]; rw [sum_eq_single vac] -- direction?
  · intro b _ hb; exact (hb (vac_only b)).elim
  simp

abbrev preGate (G : Gauge) (W : Cross L (TypeFace 1) (TypeFace 1)) := bondColor G W
abbrev lanternPhi (G : Gauge) (T : Model P K) (W : Cross P.L (TypeFace 1) (TypeFace 1)) := perched (removeGauge G T W)
-- use `Serves` & map passing any μ(n), stationary/Relative
lemma chase (T : Model S.patch S.kernel) (W : Cross S.patch.L (TypeFace 1) (TypeFace 1))
    (h : Serves G T B σ A) (hs : 0≤σ) (he : (preGate G W).strip σ C)
    (hp : Inputs S (installed S.ratio W) (B.metric.acts f) (Q.metric.acts c)) (hy : Bid.Larger (G:=G) S) (hq : Gap (B.metric.acts f) η) (hk : 0<η) :
    installed S.ratio (beams G T B) = installed S.ratio (preGate G W) + (turmoil G).acts f * installed S.ratio (lanternPhi G T W) := by
  erw [lanternPhi, perched_matters (S:=S) (removeGauge G T W)]; -- prosper
  let R:=reality S T
  have hf: installed S.ratio (beams G T B)= patron G (extracted S R (installed S.ratio W)):=
    Eq.trans (show _=predictor G R B from (hanging T B hs h S.sizes hy).symm) ((beams_exact G B Q R _ hp hy hk hq).symm)
  rw [hf,extracted, patron_plus,patron_mul, show patron G (straighten S _ (installed S.ratio W)) =_ from refreeze G T S.sizes W hs he]; rw [show patron G (installed S.ratio W)=_ from painted_copy (S:=S) G W]; rfl


section pull
variable {G : Gauge} {k n i : ℕ} {V : Text (Cloth G) (n+1)} {x : ℝ}
-- simple kinematic predicate on instantiated step equality. actual A0 fit supplies it.
variable {c f : Side}
lemma plaza_pole {α β} (j : Row α β) (H : Legs (Row α β) n) (h : Plaza H) (he : Lighthouse j) : Plaza (hitch j H) := plaza (fun k=> by cases k using Fin.cases with
   | zero=> exact he
   | succ i=> rw [hitch_succ]; obtain ⟨a,A,c,hc,hh⟩:= h; exact ⟨a,A,c,hc,hh i⟩)
lemma candleParks (h : Public V) {f c : Side} (g : Ratio c f) {B Z T : Pace g.count G}
    (hh : installed g Z= installed g B + (turmoil G).acts f * installed g T) (H : Legs (Pace g.count G) n)
    (hP : Plaza H) (hb : Lighthouse B) (hz : Lighthouse Z) (ht : Lighthouse T) :
    coupon c (n+1) (tele (install ∘ hitch Z H) V-tele (install ∘ hitch B H) V)=coupon c _ (tele (install ∘ hitch T H) (diss backed V)) := by
  rw [coupon_minus _ (h.orient (plaza_pole _ _ hP hz)) (h.orient (plaza_pole _ _ hP hb)), orient_coupon g h (plaza_pole _ _ hP hz), orient_coupon g h (plaza_pole _ _ hP hb), march_spur h, orient_coupon g (h.ascend (troops_cost ..)) (plaza_pole _ _ hP ht), ascend_coupon h (troops_cost ..)]
  let y:= (turmoil G).acts f * installed g T; let Y : Duct (Pennant G f) (Pennant G c):=fun i j=>y i j
  have hx : (fun i j=> installed g Z i j)-(fun i j=> installed g B i j)=Y := by rw [hh]; ext1 i; ext1 j; simp [Y,y]
  rw [tele_sub_fixed_finite (g:=Y) ?_]; swap
  · intro i; cases i using Fin.cases with
    | zero=> simpa only [hitch_zero,↓reduceIte]
    | succ i=> simp only [hitch_succ,sub_self, if_neg (Fin.succ_ne_zero i)]
  symm; apply tele_through; intro i x w; cases i using Fin.cases with
  | zero=> simp only [hitch_zero, troops,Y,y]; exact rfl -- `mul_apply`
  | succ i => simp only [hitch_succ,troops,crop,acts_unit,Matrix.one_apply, ite_mul,zero_mul,one_mul,hitch_succ]; simp

abbrev PathLamp {c : Side} (G : Gauge) {f : Side} (p : Ratio c f) (B Z T : Pace p.count G) := installed p Z=installed p B +(turmoil G).acts f * installed p T -- unused L
abbrev GrowsHigh {P : Patch} (G : Gauge) (B Z T : Pace P.L G) (K : KernelChoices) (D : ℕ→ Side) :=
    ∀ᶠ i in atTop, PathLamp G (draftAt P K (D i)).ratio B Z T

lemma audit_polar {P : Patch} {K : KernelChoices} {V : Text (Cloth G) (n+1)}
    {B Z T : Pace P.L G} {D : ℕ→Side} (H' : Legs (Pace P.L G) n) (hV : Public V) (h : GrowsHigh G B Z T K D) (hr : Plaza H') (hf : Lighthouse B) (hq : Lighthouse Z) (hv : Lighthouse T)
    (he : Tendsto (fun i=> (D i).val) atTop atTop) :
    tele (install ∘ hitch Z H') V-tele (install ∘ hitch B H') V=tele (install ∘ hitch T H') (diss backed V) := by
  refine coupon_high he ((hV.orient (plaza_pole _ _ hr hq)).minus (hV.orient (plaza_pole _ _ hr hf))) (?hW) (h.mono fun i hi=> candleParks hV (draftAt _ K (D i)).ratio hi H' hr hf hq hv)
  rw [march_spur hV]; exact (hV.ascend (troops_cost ..)).orient (plaza_pole _ _ hr hv)

variable {P : Patch} {J : ChartRatio G} {B Q : Bed} -- repeated B
lemma lamp_court (W : Cross P.L (TypeFace 1) (TypeFace 1)) (T : Model P K) {D : ℕ→ Side} (he : Tendsto (fun i=>(D i).val) atTop atTop) (h : Passage J B Q T)
   (hs : Serves G T B σ A) (ht : 0≤ σ) (hv : (preGate G W).strip σ x)
   (hQ : ∀ c : Side, Inputs (draftAt P K c) (installed (draftAt P K c).ratio W) (B.metric.acts (trimSide P c)) (Q.metric.acts c)) :
   GrowsHigh G (preGate G W) (beams G T B) (lanternPhi G T W) K D:= by
  refine (h.perimeter he).mono (fun i hi=>?_); obtain ⟨a,ha,hp⟩:= h.chairs ((trimSide P (D i))); exact chase (S:=draftAt P K _) T W hs ht hv (hQ _) hi hp.2 ha -- argument order
end pull
end Parapet
end YM.WilsonBulk
