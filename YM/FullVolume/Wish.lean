import YM.FullVolume.Tuned

/-! Taylor through all coordinate projection ties and classical derivative.

Smoothness to all orders is possible with the admitted ALL-period schedule
in our Run. Bounds are for each individual m (not uniform in order).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G} (M : FixedBounds C)(e : Extraction.Sequence) {n:ℕ}(p : ℕ)(v : Fin n→C.book.Token)

-- recursive in exactly lattice order

def derive (f:Points n → ℂ) : List (MotionIndex n) → (Points n → ℂ)
  | [] => f
  | a::l => fun x=> fderiv ℝ (derive f l) x (Dir a)

include M
theorem honors (l:List (MotionIndex n)) {f:Points n→ℂ}{g: MotionIndex n→Points n→ℂ} (hp:Tuned C e p v l f)
    (hh:∀ i,Tuned C e p v (i::l) (g i)) :
    ∀ x∈ NoHit C.S p n, HasFDerivAt f (stretch (fun i=> g i x)) x:= by
  intro x hx
  obtain ⟨K,hK,hT,hX⟩:= exists_compact_subset (nohitOpen ..) hx
  obtain ⟨B,r,hB,hr,H⟩:= M.taylor v l p hX hK
  let L:= stretch (fun j=> g j x)
  have hc:∀ᶠ y in 𝓝 x, ‖f y-f x-L (y-x)‖ ≤ B*‖y-x‖^2:=by
    filter_upwards [ball_mem_nhds x hr,(nohitOpen ..).mem_nhds hx] with y hy hY
    let F (x:Points n) (i : ℕ):=address (C.S.a (e i)) x
    let W (x:Points n) i:=tag (C.S.a (e i)) (F x i)
    have hv (x):Tendsto (W x) atTop (𝓝 x):=(Extraction.chosen x).comp e.cofinal
    have ht:Tendsto (fun i=>stretch (fun j=> gKernel C v (j::l) (e i) p (F x i))) atTop (𝓝 L):=
      stretching (fun j=>returns e p v (j::l) (hh j) hx (hv x))
    have he:= ((returns e p v l hp hY (hv y)|>.sub (returns e p v l hp hx (hv x))).sub (((show Continuous fun p : (Points n→L[ℝ] ℂ)×Points n => p.1 p.2 from continuous_fst.clm_apply continuous_snd).tendsto _).comp (ht.prodMk_nhds ((hv y).sub (hv x)))))
    rw [← dist_eq_norm y x]
    apply le_of_tendsto_of_tendsto he.norm (((hv y).dist (hv x) |>.pow 2).const_mul B)
    filter_upwards [e.cofinal.eventually H,(hv x).eventually (mem_interior_iff_mem_nhds.mp hT),((hv y).dist (hv x)).eventually (ge_mem_nhds (mem_ball.mp hy))] with i hi ht he using hi _ _ ht he -- refine
  rw [hasFDerivAt_iff_tendsto]; change Tendsto (fun z=> ‖z-x‖⁻¹*‖f z-f x-L (z-x)‖) _ _
  have ht : Tendsto (fun y:Points n=> B*‖y-x‖) (𝓝 x) (𝓝 0):=by
    simpa only [sub_self,norm_zero, mul_zero] using!
      (show Continuous (fun y:Points n=> B*‖y-x‖) by fun_prop).tendsto x
  refine squeeze_zero' (Eventually.of_forall (fun _=>by positivity)) ?_ ht
  filter_upwards [hc] with i hi
  apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (norm_nonneg _))).trans_eq
  rcases eq_or_ne i x with hh|hh
  · rw [hh]; simp
  have h:=norm_pos_iff.mpr (sub_ne_zero.mpr hh); field_simp

omit M in
private lemma trills (n:ℕ): ∃ L : (MotionIndex n→ℂ)→L[ℝ] (Points n→L[ℝ] ℂ),∀ v,L v=stretch v:=by
  let A : (MotionIndex n→ℂ)→ₗ[ℝ] (Points n→L[ℝ] ℂ):=
    { toFun := stretch
      map_add' := by
        intro x y; ext1 j; change ∑ i:MotionIndex n, j i.1 i.2 • (x i+y i)= (∑ i:MotionIndex n, j i.1 i.2 • x i) + (∑ i:MotionIndex n, j i.1 i.2 • y i); simp_rw [smul_add]; exact Finset.sum_add_distrib
      map_smul' := by
        intro r x; ext1 j; change ∑ i:MotionIndex n, j i.1 i.2 • (r • x i)= r • ∑ i:MotionIndex n, j i.1 i.2 • x i; rw [Finset.smul_sum]; simp [mul_left_comm] }
  exact ⟨A.toContinuousLinearMap,fun _=>rfl⟩

theorem augments (hp:Purchased C e): ∃ f:Points n→ℂ,(∀ l,Tuned C e p v l (derive f l)) ∧ ContDiffOn ℝ ∞ f (NoHit C.S p n):=by
  obtain ⟨f,hf⟩:= established M e p v hp
  let U:= NoHit C.S p n
  have H(l):Tuned C e p v l (derive f l):=by
    induction l with
    | nil=> exact hf
    | cons a l ih=>
        choose g hg using from_previous M e p v l ih
        have he (x : Points n) (hx:x ∈ U): derive f (a::l) x = g a x:=by simp only [derive]; rw [(honors M e p v l ih hg x hx).fderiv]; exact loyal ..
        refine ⟨(hg a).continuousOn.congr (fun _ hx=>he _ hx),fun K hK hk e hE=>?_⟩
        filter_upwards [(hg a).uniform K hK hk e hE] with i hi x hx; rw [he _ (hK hx)]; exact hi x hx
  refine ⟨f,H,?_⟩; obtain ⟨A,hA⟩:= trills n
  have hz (k:ℕ): ∀ l,ContDiffOn ℝ k (derive f l) U:=by
    induction k with
    | zero=> exact fun l=> contDiffOn_zero.mpr (H l).continuousOn
    | succ k ih=>
      intro l; have ht l:= honors M e p v l (H l) (g:=fun i=> derive f (i::l)) (fun i=>H (i::l)); rw [Nat.cast_add_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (nohitOpen C.S p n).uniqueDiffOn).2
      let L (x:Points n):MotionIndex n→ℂ:= fun i=> derive f (i::l) x
      have hp: ContDiffOn ℝ k L U:=contDiffOn_pi.mpr fun i=> ih _; refine ⟨by simp,A∘ L,A.contDiff.comp_contDiffOn hp, fun x hx=>?_⟩; dsimp only [Function.comp_apply]; rw [hA]; exact (ht l x hx).hasFDerivWithinAt
  exact contDiffOn_infty.mpr (fun k=> hz k [])
end YM.FullVolume
