import YM.PertExtension.HueMean
import YM.Work.G06.TurnSlot

/-! A genuine slot-polynomial presentation of the original section where
   color covariance and reality hold on the whole polynomial panel. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace YM.PertExtension.Hue
open Function Filter Set Finset MeasureTheory MvPolynomial Lattice Heat.Top Next.Rank Wilson RG Source Bid Labels Drops
open scoped Matrix.Norms.Frobenius Topology Classical BigOperators Real ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{α β :Type*}

def re (P:Poly α G):= (1/2:ℂ) • (P + Spindle.retro _ P)
lemma re_display (W : Mask α G)(P:Poly α G):display W (re P)= (↑((display W P).re):ℂ):= by
    have h := Spindle.escorted (fun i:Panel α G=> W i.1 i.2) P; unfold re
    rw [map_smul,map_add] -- order
    change display W (Spindle.retro _ P) = star (display W P) at h; rw [smul_eq_mul, (h : display _ _ = _)]
    rw [Complex.star_def,RCLike.add_conj (K:=ℂ)] -- adjust
    ring_nf; rfl
lemma re_fixes {p:Poly α G} (hp:Fixed p):Fixed (re p):=by intro u x; rw [re_display,re_display,hp u]
lemma re_clears (p:Poly α G):Clear (re p):=by intro x; rw [re_display,Complex.star_def];simp

lemma valued (P:Poly α G)(W): display W (portrait P)=∫ u:G.El,display (tint u W) P ∂G.probHaar:=by
  change (display W).toLinearMap (portrait P) = _
  rw [portrait_spec];simp only [AlgHom.toLinearMap_apply];simp_rw [← hue]

private def pin {α : Type*}{G:Gauge} (i : Panel α G→₀ℕ) : Hue.Form α G where
  toFun:=coeff i
  map_add' _ _ := coeff_add i _ _
  map_smul' x y := by rw [coeff_smul];rfl

private lemma preserve_cut (p:Poly α G)(k:ℕ) : cut k (re (portrait p))= re (portrait (cut k p)):=by
    have h₁ (q:Poly α G): cut k (re q)= re (cut k q):= by
       unfold re; rw [map_smul,map_add]
       congr 2; ext1 i; simp only [Spindle.retro,coeff_map,cut_coeff]; split_ifs <;> simp
    rw [h₁];congr 1;ext i
    have hP(q:Poly α G): coeff i (portrait q)= ∫ u:G.El,coeff i (inked u q) ∂G.probHaar:=portrait_spec q (pin i)
    rw [cut_coeff,hP,hP];simp_rw [incision,cut_coeff];split_ifs <;> simp
private lemma zero_mean (p:Poly α G)(h:p=0): re (portrait p)=0:=by
   subst p; simp [show portrait (0:Poly α G)=0 from by apply touchable;intro x; simp [valued], re, Spindle.retro]

lemma portrait_lows {m:ℕ}(p:Pose G m){n}(h:lows p n):lows (re (portrait p)) n := by
   let q:=re (portrait p)
   intro i hi
   have hu : coeff i q ≠ 0:= mem_support_iff.mp hi
   by_contra! H
   have he (j): coeff j p ≠ 0 → n ≤ Heat.Top.degree j:=by rw [degree_eq]; exact fun h' => h _ (mem_support_iff.mpr h')
   let k:=Heat.Top.degree i; have hp:cut k p=0:=by
     ext j;rw [cut_coeff,coeff_zero]
     by_contra! hb; split_ifs at hb with hh; have hz: k= Heat.Top.degree j:=hh.symm; rw [← degree_eq] at H
     exact hb (not_ne_iff.mp (mt (he _) (by omega)));exact hb rfl
   have hq : cut k q=0 := (preserve_cut p k).trans (zero_mean _ hp)
   apply hu
   calc _ = coeff i (cut k q):=by rw [cut_coeff,if_pos rfl]
        _ = 0 := by rw [hq,coeff_zero]

lemma mean_value (p:Poly α G)(W : Mask α G)(hh:∀ u:G.El,display (tint u W) p=display W p) : display W (portrait p)=display W p := (valued _ _).trans (by simp [hh])
lemma alias_gauge {m:ℕ}(B:Fin m→RG.Slot)(u:G.El)(U:CoverConfig G): tint u (mapped B U)=mapped B (Lattice.gauge (fun _=>u) U):= funext fun i : Fin m=> (Work.G06.slot_gauge (G:=G) (B i) (fun _ : Cover => u) U).symm
lemma portrait_value {m:ℕ}(p:Pose G m)(B:Fin m→RG.Slot)
   (hg:GaugeInvariant (lumin p ∘ mapped B)) (hreal:∀ z,star ((lumin p ∘ mapped B) z)= (lumin p ∘ mapped B) z) : lumin p ∘ mapped B = lumin (re (portrait p)) ∘ mapped B:=by
  funext z
  let W:Mask (Fin m) G := mapped B z
  have hh : star (display W p)=display W p:=hreal z
  have hv(u:G.El): display (tint u W) p=(lumin p ∘ mapped B) (Lattice.gauge (fun _=>u) z):=congr_arg (fun v=>lumin p v) (alias_gauge B _ z)
  change display W p = display W (re (portrait p))
  rw [re_display,mean_value p W (fun u=>(hv u).trans (hg _ z))]; exact (Complex.conj_eq_iff_re.mp hh).symm

end YM.PertExtension.Hue

namespace YM.PertExtension.Heat.Top
open Function RG Labels Source Bid
variable {G : Gauge}{d : ℕ}{F:Labels.Frame G d} (E:Data F)
structure Rendered (F:Labels.Frame G d) extends Data F where
  fixed i : Hue.Fixed (toData.shape i : Pose G (toData.count i))
  real i : Hue.Clear (toData.shape i : Pose _ _)
set_option backward.isDefEq.respectTransparency false in
def Data.color : Rendered F where
   toData := { E with shape := fun i=> Hue.re (Hue.portrait (E.shape i)), low i:=Hue.portrait_lows _ (E.low i) }
   fixed i:=Hue.re_fixes (Hue.portrait_fixed _)
   real i:=Hue.re_clears _
variable {H : Hol G}{S : SectionData F}
theorem color_acts (hv : Valid E S)(h : S.Sound H): Valid E.color.toData S:=by
  intro i;rw [hv i]
  apply Hue.portrait_value (E.shape i) (E.columns i)
  · rw [← hv i]; exact h.gaugeInvariant _
  rw [← hv i]; intro u
  rw [← h.ordinary_real]
  have hu : star (Pi.single i 1:F.Coeff)=Pi.single i 1:= by ext j; by_cases hv:j=i <;> simp [Pi.single_apply,hv]
  rw [hu]

def rendered (S : SectionData F)(p : pop S) : Rendered F := (Classical.choose (chooseData S p)).color
lemma rend_acts (h:S.Sound H)(p:pop S): Valid (rendered S p).toData S:=color_acts _ (chooseData S p).choose_spec h
end YM.PertExtension.Heat.Top
