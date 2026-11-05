import YM.Planned.PRIMARY_INTEGRAL_295.Postcards
import YM.Trace.Physicalv2.GermShiftBase

/-!
# Measuring primary output with retained fractional offsets

The one-mark input anchored at an off-center fine site \(z\), still sent to coarse
site 0, cannot just be moved with its mask to the embedded fine site 0. That
would not pay the power of block ratio needed by the one-step forward bound.
Here we address the canonical-row part. Project by the same radial charts as
the primary input at 0, but evaluate the forecast contours against the
translated stencil. Prove that *through the field engineering weight* of the
input column, this prediction still gives the same heading as in the centered
case. This is at the exact periodic/germ conventions to be paid later by the
thorn and stochastic costs; this file handles the ideal lattice predictor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Offsets
open Function Filter Set Lattice Wilson RG Source Source.Drops Labels MeasureTheory
open Planned.PrimaryIntegral295 Place Film Carrier Precision Next.Free Bloch
open Push.Local (Probe runProbe)
open Trace.Physical.GermShift
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{j t n d m:ℕ} {L:Side}

-- helper general spaces for typeclass reduction
lemma measured_power {E F:Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F](M : E→L[ℝ] F) (f:ℝ→E) (hf:ContDiffAt ℝ n f 0) (v:F)
    (he : M ∘ f=fun y:ℝ => y^m • v) (hi:n<m): M (iteratedDeriv n f 0)=0:= by
  have hv : M (iteratedDeriv n f 0) = iteratedDeriv n (M ∘ f) 0 := by
    have e : M (iteratedFDeriv ℝ n f (0:ℝ) (1:Fin n→ℝ)) = _ := DFunLike.congr_fun
      (M.iteratedFDeriv_comp_left hf le_rfl).symm (1:Fin n→ℝ)
    change _ = iteratedDeriv n (M ∘ f) 0 at e
    exact e
  rw [he,
    show iteratedDeriv n (fun y:ℝ => y^m • v) 0 = _ from
      iteratedDeriv_smul_const (f:=fun y:ℝ=>y^m) (contDiffAt_id.pow _) (x:=0) (n:=n) _,
    iteratedDeriv_fun_pow_zero, if_neg hi.ne,Nat.cast_zero,zero_smul] at hv
  exact hv
set_option maxHeartbeats 450000 in
lemma engine_through (n:ℕ)(A:Snap G d):
    throughSlot (iteratedDeriv n (fun y:ℝ => WardBin.engineered y A) 0) n:= by
  intro i hi
  let M: Snap G d →L[ℝ] Taylor G i.val := ContinuousLinearMap.proj i
  let f (y:ℝ) := WardBin.engineered y A
  have hx: M ∘ f = (fun y:ℝ => y^(i.val+2) • A i) := funext fun _=>rfl
  exact measured_power (F:=Taylor G i.val) M f (WardBin.eng_cont A n).contDiffAt (A i) hx hi

variable {p : Probe G d} {k : ℝ} (P:Flight j t)
set_option maxHeartbeats 400000 in
/-- Taylor terms of the *same history forecast* on ANY fixed stencil obey
    the polynomial-direction cancellation convention (no snapping to stencil 0). -/
lemma forecast_piece (hk:0<k) (ht:4≤t)(hd:d≤j)(q:Probe G d)(n:ℕ)(hn:n≤d)
    (S: Finset Cover) (c f:ℝ):
    ∃ v:Potential G, v∈ rangeLt (Axis→G.Color) n ∧ ping S v =
      iteratedDeriv n (Postcards.forecast S q (linesOf P k) c f) 0 := by
  let A:= trunk d (c • q.1)
  let g (x:ℝ) := WardBin.engineered x A
  let Y := Film.trace S (linesOf P k) (G:=G) (d:=d)
  have hF : ContDiff ℝ n Y := trace_smooth (stored P k hk ht) S d |>.of_le le_top
  have hG : ContDiff ℝ n g := WardBin.eng_cont A _
  have he : g 0=0:=by funext i; simp [g,WardBin.engineered_at]
  have hz(K:OrderedFinpartition n) : ∃ v:Potential G,v ∈ rangeLt (Axis→G.Color) n ∧
      ping S v = Cases.caseRead K Y g 0 1 := by
    let w(i: Fin K.length):= iteratedDeriv (K.partSize i) g 0
    let H(x:E4)(i:Axis):= iteratedFDeriv ℝ K.length (lane (G:=G) (d:=d) x i) 0 w
    have h : ∑ i,K.partSize i = n:= by simpa using K.sum_sigma_eq_sum (fun _=>(1:ℕ))
    have hH:H∈ rangeLt (Axis→G.Color) n := h ▸ lane_polynomial K.partSize w (fun _=>engine_through _ _) K.partSize_pos
    obtain ⟨u,hx,-,hp⟩:= accepts_V k hk P ht (hn.trans hd) H hH
    refine ⟨u,hx,?_⟩
    funext i
    unfold Cases.caseRead; rw [he]
    change ping S u i=iteratedFDeriv ℝ K.length (trace S (linesOf P k) (G:=G) (d:=d)) 0 w i
    rw [trace_mail (stored P k hk ht) (K.length_le.trans hn)]
    exact (congr_fun (congr_fun hp (Place.first i).val) (beam i)).symm
  choose v hv hm using hz
  refine ⟨f⁻¹ • ∑ a,v a,Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i _=>hv i)),?_⟩
  rw [map_smul,map_sum]
  change _ = iteratedFDeriv ℝ n (f⁻¹ • (Y ∘ g)) 0 1
  rw [iteratedFDeriv_const_smul_apply (hF.comp hG|>.contDiffAt),_root_.smul_apply,
      Cases.compReads hF.contDiffAt hG.contDiffAt le_rfl]
  simp_rw [hm]

variable {F:Labels.Frame G d}(M:SectionData F){A:Hol G}
/-- Unscaled field column at the *translated* stencil, with the enlarged
    support used also for the forecast comparison. -/
def there (i:F.Index)(a:Cover): Dev (translatedSupport a M.stencil) G → ℂ:=
    column M i ∘ clip G (a:=a) Finset.subset_union_right

def atColumn (i:F.Index)(a:Cover):=
    Tones.coat (there M i a) (F.grades i).2
lemma atColumn_clip (i:F.Index)(a:Cover)(f:ℝ):
    atColumn M i a f=Tones.tint M i f ∘ clip G (a:=a) Finset.subset_union_right:= by
  funext x; unfold atColumn there Tones.tint Tones.coat
  simp only [Function.comp_apply,map_smul]

-- Natural forecast when enlarging. No HEq pricing across different history.
set_option maxHeartbeats 400000 in
lemma same_trace {S T: Finset Cover}(h: S⊆T) {W : Lines L} (hw:Whole W)(p:Probe G d)
    (n:ℕ) (hn:n≤d) (x c:ℝ):
    clip G (a:=0) (show moved S 0 ⊆ T by simpa [moved] using h)
      (iteratedDeriv n (Postcards.forecast T p W c x) 0)=
    iteratedDeriv n (Postcards.forecast S p W c x) 0:= by
  let A:= trunk d (c • p.1)
  let g (x:ℝ) := WardBin.engineered x A
  let U (T:Finset Cover):Snap G d→Dev T G:= trace T W
  have hf T: ContDiff ℝ n (U T) := trace_smooth hw T d|>.of_le le_top
  have hG : ContDiff ℝ n g := WardBin.eng_cont A _
  have he : g 0=0:=by funext i; simp [g,WardBin.engineered_at]
  let V:Dev T G →L[ℝ] Dev S G:=clip G (a:=0) (moved_zero ▸ h)
  change V (iteratedFDeriv ℝ n (x⁻¹ • (U T ∘ g)) 0 1) = iteratedFDeriv ℝ n (x⁻¹ • (U S ∘ g)) 0 1
  rw [iteratedFDeriv_const_smul_apply ((hf T).comp hG|>.contDiffAt),
    iteratedFDeriv_const_smul_apply ((hf S).comp hG|>.contDiffAt),_root_.smul_apply,_root_.smul_apply,map_smul,
    Cases.compReads (hf T|>.contDiffAt) hG.contDiffAt le_rfl,
    Cases.compReads (hf S|>.contDiffAt) hG.contDiffAt le_rfl,map_sum]
  refine congr_arg (x⁻¹ • ·) (Finset.sum_congr rfl (fun K _=>?_))
  unfold Cases.caseRead; rw [he]; funext i
  let w (i:Fin K.length):=iteratedDeriv (K.partSize i) g 0
  change iteratedFDeriv ℝ K.length (trace T W (G:=G) (d:=d)) 0 w (moveSpot _ i)=iteratedFDeriv ℝ K.length (trace S W (G:=G) (d:=d)) 0 w i
  rw [trace_mail hw (K.length_le.trans hn),trace_mail hw (K.length_le.trans hn),show (first (moveSpot _ i)).val=(first i).val+0 from rfl,add_zero]
  exact rfl

set_option maxHeartbeats 600000 in
/-- The offset-column prediction has the same full jet through the input
    column's weight, hence the same rows there. Higher field rows not asserted
    (will need upper triangular and cone estimates). -/
lemma predicts (hk:0<k)(ht:4≤t)(hd:d≤j)(hc:M.Sound A)
    (i:F.Index)(q:Probe G d)(hs:q.2.val ≤ (F.grades i).1)(a:Cover)(c f:ℝ):
      iteratedDeriv q.2.val (atColumn M i a f ∘
        Postcards.forecast (translatedSupport a M.stencil) q (linesOf P k) c f) 0 =
      iteratedDeriv q.2.val (Tones.tint M i f ∘ Postcards.forecast M.stencil q (linesOf P k) c f) 0:= by
  let n:=q.2.val
  let S:=M.stencil
  let A':=translatedSupport a S
  let h (T:Finset Cover):=Postcards.forecast T q (linesOf P k) c f
  have hp T: ContDiff ℝ n (h T) := (Postcards.forecast_truth T q _ _ _ (stored P k hk ht)).of_le le_top
  let g:= column M i
  let t:= (F.grades i).2
  have hg: ContDiff ℝ ω g := column_smooth M i
  have hl: ContDiff ℝ ω (there M i a) := hg.comp (clip G (a:=a) (T:=A') (S:=S) Finset.subset_union_right).contDiff
  change iteratedFDeriv ℝ n (atColumn M i a f ∘ h A') 0 1=iteratedFDeriv ℝ n (Tones.tint M i f ∘ h S) 0 1
  rw [Cases.compReads (g:=atColumn M i a f) ((Tones.coat_smooth hl t f).contDiffAt.of_le (m:=↑n) le_top) (hp _|>.contDiffAt) le_rfl,
      Cases.compReads (g:=Tones.tint M i f) ((Tones.coat_smooth hg t f).contDiffAt.of_le (m:=↑n) le_top) (hp _|>.contDiffAt) le_rfl]
  refine Finset.sum_congr rfl (fun K _=>?_)
  choose v hv he using fun i: Fin K.length=>forecast_piece P hk ht hd q (K.partSize i)
    ((K.partSize_le i).trans (hs.trans (F.bound _))) A' c f
  let u(i:Fin K.length):=ping A' (v i)
  let x(T:Finset Cover)(i:Fin K.length):=iteratedDeriv (K.partSize i) (h T) 0
  have H : ∑ i,K.partSize i=n:=by simpa using K.sum_sigma_eq_sum (fun _=>(1:ℕ))
  let ψ : CoverConfig G → ℂ:= M.evaluate (copy F i)
  have hl' : LocalOn S ψ:= M.cylinder_local _
  have hN: Null (F.grades i).1 S ψ:= fun _ _ hw _ _ hu => lower A M hc i _ hw _ hu
  let Za : moved M.stencil a ⊆ A' := Finset.subset_union_right
  let β₀ : S⊆A':= Finset.subset_union_left
  let Z := clip G (a:=0) (T:=A') (S:=S) (moved_zero ▸ β₀)
  have hT₁ := translate_equal_jet (a:=a) hl' (hg.contDiffAt.of_le (m:= ↑(F.grades i).1) le_top)
    hN (K.length_le.trans hs) K.partSize (H.trans_le hs) v hv A' β₀ Za
  unfold Cases.caseRead; change iteratedFDeriv ℝ K.length (atColumn M i a f) (h A' 0) (x A')=iteratedFDeriv ℝ K.length (Tones.tint M i f) (h S 0) (x S)
  have hψ: ψ ∘ pore (S:=A') = g ∘ Z := by
    change ψ ∘ pore (S:=A') = (ψ ∘ pore (S:=S)) ∘ clip G (a:=0) (S:=S) (T:=A') (moved_zero ▸ β₀)
    simpa only [show Lattice.translate (0:Cover) = (@id (CoverConfig G)) from funext (fun U=>funext fun j=>by unfold Lattice.translate;simp),Function.comp_id]
      using translated_masked hl' (a:=0) (T:=A') (moved_zero ▸ β₀)
  rw [show h A' 0 = 0 from Postcards.forecast_zero ..,show h S 0=0 from Postcards.forecast_zero ..,
      atColumn, Tones.tint, Tones.color_jet hl,Tones.color_jet (column_smooth M i), smul_apply,smul_apply, smul_zero,smul_zero]
  refine congr_arg (_ • ·) ?_
  rw [show x A'=u from (funext he).symm]
  change iteratedFDeriv ℝ K.length (there M i a) 0 u=_
  rw [translated_masked hl' Za, hψ] at hT₁
  refine hT₁.trans ?_
  rw [Next.Foundations.jets_linear Z (hg.contDiffAt.of_le (m:=↑K.length) le_top)]
  refine congr_arg (iteratedFDeriv ℝ K.length g 0) ?_
  exact funext (fun i=> (congr_arg Z (he i)).trans
    (same_trace β₀ (stored P k hk ht) q _ ((K.partSize_le i).trans (hs.trans (F.bound _))) _ _))
end YM.RG05Readout.Offsets
