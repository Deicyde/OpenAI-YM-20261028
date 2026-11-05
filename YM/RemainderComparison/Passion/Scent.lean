import YM.RemainderComparison.Passion.Supplied
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
namespace SeatD
variable (S:SeatD G n) (X:Hol G) (K:Support n) (M:MaskType)
local notation "hold'" => Local.joint S.sectionQ S.origin K
local notation "A'"=> S.basis
local notation "e₀"=> S.basis.e0
local notation "L₂"=> seeing S K M
variable (z:ℝ)
lemma fragile : S.realD ((SeatD.pure S z).header):=by
    unfold realD; funext i; by_cases hi:i=0 <;> simp [SeatD.pure,Labels.Frame.e0,hi]
lemma icy : S.basis.core ((SeatD.pure S z).header) =0:=by
    unfold SeatD.pure; funext i; by_cases h:i=0 <;> simp [Labels.Frame.core,Labels.Frame.e0,h]
lemma snowy : Core p S X K M (SeatD.pure S z):=by
    have hg: (Complex.ofReal ∘ ((SeatD.pure S z).entry))=0 := rfl
    constructor
    · exact SeatD.fragile ..
    · unfold chord; rw [icy, map_zero]
      exact CouplingShape.reg_const 0 -- find
    · exact CouplingShape.reg_const 0
    rw [hg]; exact (reads_null_iff ..).mpr ⟨rfl,fun _ _=> ⟨contDiffAt_const,fun k _=>by simp⟩⟩
lemma pure_identity (U:Config G n): sharp p S K M (SeatD.pure S z) U=z:=by
    unfold sharp chord; rw [icy,map_zero]; unfold SeatD.pure; by_cases h:Healthy p.threshold L₂ U
    all_goals by_cases hv :Healthy p.threshold hold' U
    all_goals simp [Labels.Frame.e0,h,hv,masked_eq,masked_ne]
lemma pale(w:ℝ)(h:‖z‖ ≤ w): Palette p S K M (SeatD.pure S z) S.origin w:=by
    have hw:0≤ w:= (norm_nonneg _).trans h
    constructor
    · unfold Labels.Frame.coeffSize SeatD.pure; rw [Finset.sum_eq_single (0:S.basis.Index)]
      · simp [Labels.Frame.e0]; exact h
      · intro i _ hi; simp [Labels.Frame.e0,hi]
      simp
    · exact VerifiedReset.sup_le (VerifiedReset.sup_const 0) (by simpa)
    unfold chord; rw [icy,map_zero]; exact VerifiedReset.sup_le (VerifiedReset.sup_const 0) (by simpa) -- edit

-- Linearity with families.USOM η. Include budget.P.Proof used for canonical choices.
variable (g: θ)(f:Audited Q→ Config G n→ℝ) (R':Audited Q→ PairD S)
structure Depends (D:Finset θ)(F:Audited Q → PairD S): Prop where
    labels : ∀ a b,(∀ i∈D,a i=b i)→ (F a).header=(F b).header
    pay (i:θ): i∈D → ∀ (a:Audited Q)(b c d: Solos.Scope Q i)(z y: ℝ), b.val=z • c.val+y • d.val → (F (Function.update a i b)).header=(↑z:ℂ) • (F (Function.update a i c)).header+(↑y:ℂ) • (F (Function.update a i d)).header
    line x: LinearP D (fun v=> (F v).entry x)
variable {D₀: Finset θ}
lemma Depends.era (H:Depends S D₀ R') (U:Config G n): LinearP D₀ (fun b=> sharp p S K M (R' b) U):=by -- arg S?
    let C b:= (R' b).header
    let t p' := RG.masked p.threshold L₂ (fun V=> (S.chord p p' V).re)
    let W (f: Config G n→ℝ) := RG.masked p.threshold hold' f
    have hm:LinearP D₀ (fun z=> W ((R' z).entry) U):=by
       by_cases h:Healthy p.threshold hold' U
       · unfold W; simp_rw [fun z=> RG.masked_eq p.threshold hold' ((R' z).entry) U h]; exact H.line U
       unfold W; simp_rw [fun z=> RG.masked_ne p.threshold hold' ((R' z).entry) U h]; exact LinearP.nil _
    have he:LinearP D₀ (fun z=> (C z 0).re):=by
       refine ⟨fun a b hi=> congr_arg (fun p':S.basis.Coeff=> (p' 0).re) (H.labels a b hi),fun i hi a b c d z y hp=>?_⟩
       unfold C; rw [H.pay i hi a b c d z y hp]; simp
    apply LinearP.plus (LinearP.plus he (f:=(fun z=> (C z 0).re)) (g:= fun z=> t (C z) U) ?_) hm
    refine ⟨fun a b hi=> congr_arg (fun p': S.basis.Coeff=> t p' U) (H.labels a b hi),fun i hi a b c d z y hp=>?_⟩; unfold C; rw [H.pay i hi a b c d z y hp]; by_cases h: Healthy p.threshold L₂ U
    · unfold t; rw [RG.masked_eq _ _ _ _ h,RG.masked_eq _ _ _ _ h, RG.masked_eq _ _ _ _ h]; simp [chord]
    unfold t; rw [RG.masked_ne _ _ _ _ h,RG.masked_ne _ _ _ _ h,RG.masked_ne _ _ _ _ h]; simp
variable {w:ℝ}
lemma wistful (h: Local.Readable X S.sectionQ p n w)(hi:∀ v,p.Regular K (f v)) (he:∀ U,LinearP D₀ (fun b=> f b U)): Depends S D₀ (fun v=> sector p S X K (f v)):=by
    let V u:= sector p S X K (f u); let t b:= cx (f b); let d:= S.degree; have hv u:p.Regular K (t u):= regular_mapped Complex.ofRealCLM (hi u)
    have hg (a:Audited Q)(i:θ)(hξ:i∈D₀) (u v w': Scope Q i) (z y:ℝ) (hp:u.val=z • v.val+y • w'.val) : t (Function.update a i u)=(z:ℂ) • t (Function.update a i v)+(y:ℂ) • t (Function.update a i w'):= by
       funext U; dsimp only [t,cx,Function.comp_apply]; simp only [(he U).draws i ‹_› a u v w' z y hp, Pi.add_apply,Pi.smul_apply, Complex.ofReal_add,Complex.ofReal_mul]; rfl
    have hf (a b:Audited Q)(h:∀ j∈ D₀,a j=b j) : f a=f b:= funext fun U=> (he U).frame a b h
    have ht(a:Audited Q)(i:θ)(ha:i∈D₀) (u v w':Scope Q i)(z y:ℝ)(hU:u.val=z • v.val+y • w'.val): (V (Function.update a i u)).header=(z:ℂ) • (V (Function.update a i v)).header+(y:ℂ) • (V (Function.update a i w')).header:=by
       change Local.weighted _ S.basis _ _ _ (t _) = _; unfold Local.weighted; rw [hg a i ha u v w' z y hU,project_add X S.origin (regular_smul _ (hv _)) (regular_smul _ (hv _)) h.order,project_smul X _ _ (hv _) h.order,project_smul X _ _ (hv _) h.order,map_add,map_smul,map_smul,map_add,map_smul,map_smul]; rfl
    refine ⟨fun a b h=> congr_arg (fun x=>(sector p S X K x).header) (hf a b h),fun i hi a=>ht a i hi,fun U=> ⟨fun a b hi=> congr_arg (fun x=>(sector p S X K x).entry U) (hf a b hi),fun i hi a b c d z y hB=>?_⟩⟩
    change ( (t (Function.update a i b) U) -(Local.presented S.sectionQ S.origin _ (V (Function.update a i b)).header U)).re= _; rw [hg a i hi b c d z y hB,ht a i hi b c d z y hB,map_add,map_smul,map_smul]
    unfold sector Local.residual; simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply, smul_eq_mul,Complex.sub_re, Complex.add_re,Complex.re_ofReal_mul]; ring_nf; rfl
lemma limber {f : Audited Q→ℝ}(h:LinearP D₀ f): Depends S D₀ (fun v=> SeatD.pure S (f v)):=by
   refine ⟨fun a b hi=> congr_arg ((SeatD.PairD.header)∘ SeatD.pure S) (h.frame a b hi),fun i hi a x b c y z hv=> ?_, fun X=> LinearP.nil _⟩
   unfold SeatD.pure; simp only [h.draws i hi a x b c y z hv,Complex.ofReal_mul,Complex.ofReal_add]; rw [add_smul,←smul_smul,← smul_smul]
end SeatD
end YM.RemainderComparison.Passion
