import YM.RG08.Apex.Polar
/-! # Checks. Density normalization germ pays scalar outside,
transported verbatim. First post-stencil nontrivially iterated.
No identification here with extractions, even E loop column. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free Matrix Tree
open scoped BigOperators Topology Real Classical Matrix.Norms.Frobenius
open Chain Wings
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {c f : Side} {r k : ℕ} {α:Type} [Fintype α] {Q : Row α α}

-- not the output of a step relative to a normalized probability in V; pull through the exact scalar verbatim
lemma local_noise_germ (S : StepData c f)(t:S.Choices)(h : S.patch.Branches S.kernel G) : ∀ᶠ U : Config G f in 𝓝 1, ∀ V : Config G c,∀ β:ℝ,
    S.density β U V=((S.penaltyZ β G)⁻¹)^Fintype.card (Edge (Site c))*Real.exp (-β * tickets S V (S.prediction U t)) := by
  filter_upwards [collapse_tags S t h] with U hu
  intro V β; rw [hu]; unfold StepData.noise StepData.penaltyWeight tickets
  rw [Finset.prod_mul_distrib,Finset.prod_const, card_univ, ← Real.exp_sum]; congr 2; rw [← Finset.mul_sum]; ring

-- affine + Gaussian inherited at first loops
lemma issue {i N : ℕ} (hp : X.Wake G) (hv : LocalRatio D) (hi:i<N) :
    X.album ν D N i 1 3 = feather (X.album ν D N (i+1) 1 3) (predict G X N i)+scrollL (blot ν (X.patch i) X.kernel.penalty 3) (scan (predict G X N i)) := by
  let A := X.album ν D N (i+1); let p:=X.patch i; let Q:=predict G X N i; let F:= awakening ν p D X.kernel.penalty A
  let M:= curve G X N i
  let V:= X.history N (i+1)
  have he:Whole Q:=(lenders G X.kernel).elim fun Y=> ⟨_,_,Y.wpos _,(report_funding X hp Y i N).2⟩
  have ha:= X.packing ν D hp hv hi; have hT:Whole M:= (lenders G X.kernel).elim fun Y=> ⟨_,_,Y.wpos _,(report_funding X hp Y i N).1⟩
  have hh := veiled_whole hT
  have hF : Gets F:= Gets_awake p D X.kernel ν ha.1
  have hy : afterT (veiled M) F none 1 1 3=0:= sum_eq_zero fun i _=> by rw [not_ne_iff.mp (mt (treble_reel hh (fun i j=> (hF.2 i j).1) hF.1) (fun hx=> by have hy:= hx.2; omega)), smul_zero]
  have hx : luggage ν p D X.kernel 1 3= -(blot ν p X.kernel.penalty 3):= by simp [luggage]
  have hQ: Whole (scan Q) := scan_whole he; have hB:= (blot_sym p ν X.kernel.penalty (r:=3)).1
  rw [album_step X ν D hi,correct_p ν _ _ (q:=0) (by decide) (by decide) (by decide),reviseLead,sector_unique (e:=1) _ _ (by decide) (by decide) (by decide)]
  change strike ν p _ X.kernel (X.trees i) (X.history N (i+1)) _ 1 3=_
  rw [division ν p D X.kernel _ _ (hp i) ha.1 ..]; congr 1
  change -scrollL (luggage ν p D X.kernel 1 3 + afterT (veiled M) F none 1 1 3) (scan Q)=_
  rw [hy,hx,add_zero];
  let B:= blot ν p X.kernel.penalty 3
  have ht := scroll_less (show Summable (0:Shale (Park G (p.L)) 3) from summable_zero) hB hQ
  simp only [nobody _ hQ, zero_sub] at ht; rw [ht,neg_neg]
lemma probe_check (F : Air G) (ν : G.ColorIndex) : reform (compass ν F) 1=probeK ν (F (2*1) 2) := by
  rw [show (1:ℕ)=0+1 from rfl,reform_succ, Finset.sum_range_one]; simp [powT,reform_zero,Conductor.compass]
end YM.RG08
