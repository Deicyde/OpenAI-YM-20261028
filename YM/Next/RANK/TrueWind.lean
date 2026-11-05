import YM.Next.RANK.Course
import YM.Next.RANK.Insiders

/-!
# W in the old calibrated physical history

Prove reality of the in-chamber WHOLE regular function (using the whole exact
transport on the C.beta law), even though not assumed for the intermediate H
lists. Unit, real and linear hold there. Consequently available for Taylor on
log directions IN that mask when all are small, later transporting those
consequences to shorter stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Filter Set Lattice Wilson RG Extraction Labels Source Source.Drops
open Configuration Normal Rise MvPolynomial MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}
variable (C : Family G) {N p k d b : ℕ}

private lemma when_all (R : Rep G n) (U : Config G n) (hr : flags R.p.threshold U = ∅) (F : Frame G d) (S : SectionData F) (P : Coefficient F n) :
    0 < R.eval U ∧ P.density 0 S R U = (R.eval U:ℂ) * P.exponentialEntry 0 S R U := by
  refine ⟨?_,?_⟩
  · unfold Rep.eval; rw [Activities.gas_one _ _ hr, mul_one]; exact Real.exp_pos _
  have hg (p : Finset ℕ) : P.marked R p U=0 := by
    unfold Coefficient.marked; split; swap; · rfl
    rename_i h
    obtain hv|⟨i,hi⟩:=p.eq_empty_or_nonempty
    · subst p; exact Finset.sum_empty
    have hx : ((R.activities.forced i).inventory)⊆ Finset.biUnion p (fun i=> (R.activities.forced i).inventory) := Finset.subset_biUnion_of_mem (fun i => (R.activities.forced i).inventory) hi
    rw [h.2, hr] at hx; exact False.elim ((R.activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp hx))
  unfold Coefficient.density; simp_rw [hg]; simp

def awakeFull (k N p : ℕ) (v : C.label d) (U) := pinHat C d k * (parcel C d k N p v).exponentialEntry 0 (C.localSection d) (C.path.rep N p k) U

lemma flows_add (C : Family G) (X : Course C N p k) (F F' : Config G (C.side N p) → ℂ)
    (hi : Integrable F (prior G (C.side N p))) (hh : Integrable F' (prior G (C.side N p))) (m : ℕ) (h : m≤N) : X.flow (F+F') m h=X.flow F m h+X.flow F' m h := by
  induction h using Nat.decreasingInduction with
  | self => rw [Course.flow_self,Course.flow_self,Course.flow_self]
  | of_succ j hj IH =>
    rw [X.flow_step _ _ hj,X.flow_step _ _ hj,X.flow_step _ _ hj,IH]; exact StepData.push_add (C.path.levels.transition_mass ..) _ _ (X.flow_int _ hi _ hj) (X.flow_int _ hh _ hj)
lemma flows_smul (C : Family G) (X : Course C N p k) (F : Config G (C.side N p) → ℂ) (hi : Integrable F (prior G (C.side N p))) (s : ℂ) (m) (h : m≤N) :
    X.flow (s • F) m h=s • X.flow F m h := by
  induction h using Nat.decreasingInduction with
  | self => rw [Course.flow_self,Course.flow_self]
  | of_succ j hj IH => rw [X.flow_step _ _ hj,X.flow_step _ _ hj,IH]; exact StepData.push_smul _ _ _ s (X.flow_int _ hi _ hj)
lemma flows_star (X : Course C N p k) (F : Config G (C.side N p) → ℂ) (hI : Integrable F (prior G (C.side N p))) (m) (hm : m ≤ N) :
    X.flow (star F) m hm=star (X.flow F m hm) := (X.flow_linear F (starL' ℝ (A:=ℂ)).toContinuousLinearMap hI m hm).symm

variable {C} (h : C.Makes) (h₁ : C.ref d ≤ k) (h₂ : k ≤ N)

def singleP (C : Family G) (N p : ℕ) (v : C.label d) : Config G (C.side N p) → ℂ := fun x => (bare (C.beta N p) x:ℂ)*C.O N p v 0 x
lemma singleP_int (C : Family G) (N p : ℕ) (v : C.label d) : Integrable (singleP C N p v) (prior G _) :=
    ((Complex.continuous_ofReal.comp (bare_cont _)).mul (C.continuousO _ _ _ _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
include h h₁
lemma rates_arc (X : Course C N p k) (v : C.label d) (m : ℕ) (hm : m≤ N) (hk : k≤m) :
    let P:= C.path.rep N p m; let F:=parcel C d m N p v
    pinHat C d m • F.density 0 (C.localSection d) P = X.flow (singleP C N p v) m hm := by
  let V:= C.localSection d
  let A:= C.factory d N p
  have he:=h.calibrated d N p (h₁.trans (hk.trans hm))
  dsimp only; induction hm using Nat.decreasingInduction with
  | self =>
    rw [Course.flow_self]; funext i
    rw [Pi.smul_apply, smul_eq_mul,parcel,he.encode]; unfold singleP pinHat
    rw [(h.wilson.starts N p).2, ← mul_assoc,← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')), one_mul]; rfl
  | of_succ j hj IH =>
    let s:= C.S.block j; let W:= C.path.rep N p (j+1)
    let S:= (C.path.levels.clock.op j p)
    let F:= parcel C d (j+1) N p v
    have hv:= h₁.trans (hk.trans (Nat.le_succ _))
    have hQ : Integrable (F.density 0 V W) (prior G _):= TransferData.density_int h.wilson he _ _ hv hj
    rw [Course.flow_step _ _ j hj, ← IH (hk.trans (Nat.le_succ _)), parcel, he.unnormalized _ (h₁.trans hk) hj, X.same _ (hk.trans (Nat.le_succ _)) hj,
      S.push_smul (F.density 0 V W) _ _ hQ]
    rw [smul_smul, show pinHat C d j * ((C.S.block j).val:ℂ)^d=pinHat C d (j+1) from ?_]; rfl
    unfold pinHat; rw [C.S.a_step]; simp only [Complex.ofReal_div,Complex.ofReal_natCast, div_pow,inv_div]; rw [div_eq_mul_inv,mul_comm]
include h₂

omit h₁ in
lemma X_choose (p : ℕ) : Nonempty (Course C N p k) := by
  exact ⟨⟨C.path.β N p, h₂,fun _ _ _=>rfl, fun _ h₃=> Overlay.beta_positive h.wilson h₃⟩⟩

-- linears on ALL healthy. unit preserved exactly.
lemma on_branch (p : ℕ) (U : Config G (C.side k p)) (hp : flags (C.path.rep N p k).p.threshold U=∅) :
    ∀ (v : C.label d), awakeFull C k N p (star v) U=star (awakeFull C k N p v U) ∧ awakeFull C k N p (C.refUnit d) U=1 ∧
      ∀ w a, awakeFull C k N p (v+a • w) U= awakeFull C k N p v U + a*awakeFull C k N p w U := by
  obtain ⟨X⟩ := X_choose (h:=h) (h₂:=h₂) p
  let R:= C.path.rep N p k; let V:= C.localSection d
  let F:= singleP C N p (d:=d); let f v:= awakeFull C k N p (d:=d) v U
  have hv (v) := rates_arc (h:=h) (h₁:=h₁) X v k h₂ le_rfl
  let q:= R.eval U
  have hy (v : C.label d) := when_all R U hp (C.labels.level d) V (parcel C d k N p v)
  intro v
  have hq : (q:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hy v |>.1.ne')
  have hs : C.ref d ≤ N := h₁.trans h₂
  have ht v : (q:ℂ)* f v=X.flow (F v) k h₂ U := by
    rw [← (show _=X.flow (F v) k h₂ from hv v),Pi.smul_apply,smul_eq_mul]; rw [(hy v).2]; unfold f awakeFull
    exact mul_left_comm ..
  refine ⟨mul_left_cancel₀ hq ?_,mul_left_cancel₀ hq ?_,fun w a=> mul_left_cancel₀ hq ?_⟩
  · have he : F (star v)=star (F v) := by ext1 i; simp only [F,Pi.star_apply,singleP, Family.reality C h hs];simp
    change _ * f (star v)=(q:ℂ)*star (f v); rw [ht,he,flows_star C X _ (singleP_int ..),Pi.star_apply,← ht]; simp [mul_comm]
  · let b:= C.beta N p; let L:=Complex.ofRealCLM; let t:= bare (G:=G) (n:=C.side N p) b
    have he : F (C.refUnit d)=L∘t := by funext i; simp only [F,singleP,C.constant h d hs,Pi.one_apply,mul_one];rfl
    change _* f (C.refUnit d)=_; rw [ht,he,← X.flow_linear t L (bare_integrable _),mul_one, Function.comp_apply]; apply congr_arg (fun x : ℝ => (x:ℂ)); exact congr_fun (X.vacuum_at h k h₂ le_rfl) U
  · change (q:ℂ)*f (v+a • w)= (q:ℂ)* (f v+a*f w)
    have he : F (v+a • w)= F v+a • F w := by
      funext x; have hv:= C.linearO N p d (0:Site (C.side N p)); unfold F singleP
      rw [show C.O N p (v+a • w) 0= _ from hv.map_add .., show C.O N p (a • w) 0= _ from hv.map_smul ..]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
    rw [ht,he,flows_add _ X _ _ (singleP_int ..) ((singleP_int C N p w).smul a),flows_smul _ _ _ (singleP_int ..),Pi.add_apply,Pi.smul_apply, smul_eq_mul,← ht,← ht];ring

lemma sections_true (p : ℕ) (i : ℕ) (v : C.label d) (U : Config G (C.side k p)) (hp : flags (C.path.rep N p k).p.threshold U=∅) :
    nearHol C v i k N p U+wideHol C v i k N p U= awakeFull C k N p v U := by
  let W:= C.path.rep N p k; let H:= parcel C d k N p v; let V:= C.labels.level d; let O:= C.localSection d; let o : Site (C.side k p) := 0
  have hv := h.calibrated d N p (h₁.trans h₂)
  have hs : H.remBound 0 W _ _ := hv.cap k h₁ h₂ _
  let P a := H.regular a U; let B:= nearX C v i k N p; let t:= W.p.threshold
  let c := pinHat C d k
  have ht (i : ℕ): H.maskedTerm W i U=P i := by unfold Coefficient.maskedTerm; rw [masked_eq _ _ _ _ (by simp [Healthy,hp,W])]
  have hu : Summable P := ((Coefficient.regular_series hs).summable U).congr ht
  let S:=setOf (smalls C i k N p v)
  have hA:= Summable.tsum_add_tsum_compl (s:=S) (f:=P) (hu.subtype S) (hu.subtype Sᶜ)
  let X a := nearW C v i k N p a*nearA C v i k N p a U
  have he (a : S) : X (Sum.inr a)= c*P a.val := by change c*1*P a.val= _; rw [mul_one]
  have hX : Summable (X∘Sum.inr) := ((hu.subtype S).mul_left c).congr (fun a=> (he a).symm)
  change (∑' a,X a)+(∑' a : ↥(Sᶜ),c*P a.val)=c*H.exponentialEntry 0 O W U
  rw [Summable.tsum_sum (f:=X) (hasSum_fintype _).summable hX,tsum_fintype]; simp_rw [he]; rw [tsum_mul_left,tsum_mul_left,add_assoc,←mul_add]
  change (∑ b,X (Sum.inl b)) + c*((∑' x:S,P x.val) +∑' x:↥(Sᶜ),P x.val) = _
  rw [hA]
  rw [Coefficient.exponentialEntry, masked_eq W.p.threshold _ _ _]
  · simp_rw [ht]; rw [mul_add]; congr 1
    -- read Section polynomial on coordinates
    let N:= V.scaled t⁻¹ (V.core H.x)
    have hg : N=∑ i,N i • Pi.single i 1 := by ext1 i;simp [Pi.single_apply]
    unfold LA X nearA nearW; rw [Fintype.sum_sum_type,Fintype.sum_unique]
    change c*H.x 0 * 1+(∑ i,c*N i*O.places (Pi.single i 1) o U)=c*(H.x 0+O.places N o U)
    have hf : ∑ i : V.Index,N i*O.places (Pi.single i 1) o U=O.places N o U := by
      conv_rhs => rw [hg]
      unfold SectionData.places SectionData.evaluate; rw [map_sum,map_sum]; simp_rw [map_smul]; rfl
    rw [mul_one,mul_add,←hf,Finset.mul_sum]; simp only [mul_assoc]
  unfold Healthy; rw [show flags _ _=_ from hp]; simp
end YM.Next.Rank.Spindle
