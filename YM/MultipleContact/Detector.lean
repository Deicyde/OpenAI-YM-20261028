import YM.MultipleContact.Fields
import YM.Work.A04

/-! Fixed, finite tomography per output horizon. Not an assertion yet that it matches the approaching cluster. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact
open Set Function Filter MeasureTheory Table Extraction Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G:Gauge}{L:Register G}{S T:Table L}{d h n:ℕ}
variable {P: DiffPlan S} {X:Rotation S}

def response (T:Table L) (h:ℕ) (x:Exterior L) : S.Field h→ₗ[ℂ] ℂ := (T.injectFront x.letter x.point h).comp (S.representative h)
lemma response_self (x:Exterior L) (v:S.Field h) : response S h x v=S.spectra h v x:=by
     obtain ⟨w,hw⟩:= S.onto h v; rw [← hw,S.projected]
     change S.replies h (S.representative h (S.project h w)) x = _
     exact congr_fun (by
       apply sub_eq_zero.mp
       rw [← map_sub]
       exact (Submodule.Quotient.mk_eq_zero _).mp (by change S.project h ((S.representative h (S.project h w))-w)=0; rw [map_sub,S.rep,sub_self])) x

structure Detector (S:Table L) (h:ℕ) where
  probes : Finset (Exterior L)
  decode : (probes→ℂ)→ₗ[ℂ] S.Field h
  fixes (x) : decode (fun e:probes=>response S h e x)=x

lemma detector_exists (h:ℕ) (S:Table L) : Nonempty (Detector S h):=by
  let r:= response (S:=S) S h
  obtain ⟨D,hD⟩:=YM.Work.A04.finite_faithful r (by
    intro a b he
    exact S.faithfully h (funext fun x:Exterior L=>by simpa only [LinearMap.pi_apply,r,response_self] using (congr_fun he x)))
  let t:=LinearMap.pi fun i:D=> r i
  let u:=t.leftInverse
  exact ⟨D,u,fun x=> t.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hD) x⟩

def joint (e : Exterior L) (z : Points n) : Points (n+e.n):=
   points (Fin.append (fun i:Fin n=>z i+e.point 0) (Points.tail e.point).ofLp)
lemma joint_clear (e : Exterior L){δ:ℝ} (hh:∀ i:Fin e.n,δ≤ ‖e.point i.succ - e.point 0‖)
    (z : Points n)(hz:∀ i:Fin n,‖z i‖<δ)(hx:z∈conf n):joint e z∈conf (n+e.n):=by
  have he i:joint e z (Fin.castAdd e.n i)= z i+e.point 0:= by simp [joint]
  have hw i:joint e z (Fin.natAdd n i)=e.point i.succ:=by simp [joint,Points.tail]
  have hl(i:Fin n)(j:Fin e.n):z i+e.point 0≠ e.point j.succ :=by
       intro H
       have hl : z i=e.point j.succ-e.point 0:= eq_sub_of_add_eq H
       have hp:= hz i; rw [hl] at hp; exact not_lt_of_ge (hh j) hp
  change Injective _
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      exact congr_arg (Fin.castAdd e.n) (hx (by simpa only [he,add_left_inj] using hij))
    intro j hij
    exact False.elim (hl i j (by simpa only [he,hw] using hij))
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro j hij
    exact False.elim (hl j i (by simpa only [hw,he] using hij.symm))
  intro j hij
  refine congr_arg (Fin.natAdd n) (Fin.succ_inj.mp (e.clear (?_)))
  simpa only [hw] using hij

lemma detector_clearance (D : Detector S h) : ∃ δ:ℝ,0<δ ∧ ∀ e∈D.probes, ∀ i:Fin e.n,2*δ≤ ‖e.point i.succ - e.point 0‖:=by
   have he(x:D.probes)(i:Fin x.val.n):0 < ‖x.val.point i.succ-x.val.point 0‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (x.val.clear.ne (Fin.succ_ne_zero _)))
   have ht (x:D.probes)(i:Fin x.val.n): ∀ᶠ δ:ℝ in 𝓝 (0:ℝ),2*δ≤ ‖x.val.point i.succ-x.val.point 0‖:=by
       filter_upwards [(gt_mem_nhds (by linarith [he x i] : (0:ℝ)< ‖x.val.point i.succ-x.val.point 0‖ /2))] with δ hh
       exact by linarith only [hh]
   have ht':= eventually_all.mpr fun i=> eventually_all.mpr fun j=>Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s:=Ioi 0)) (ht i j)
   obtain ⟨δ,hδ,h⟩:= (ht'.and (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0))).exists
   exact ⟨δ,h,fun e he i=>(hδ ⟨e,he⟩) i⟩

-- Cluster readings as numerical functions. Exteriors initially on reference labels.
def tagsPlaced (q:Fin n→S.Tag) (e:Exterior L):(Fin (n+e.n)→S.Tag):= Fin.append q (S.classTokens ∘ e.letter)
def raw (T:Table L)(q:Fin n→S.Tag)(z:Points n)(e:Exterior L):ℂ:= S.useAt T (joint e z) (tagsPlaced q e)
def Detector.apply (D : Detector S h)(q:Fin n→S.Tag)(z:Points n): S.Field h:= D.decode (fun e:D.probes=> raw S q z e)
end YM.MultipleContact
