import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Wiggle
/-!
# Exterior broad masks can be paid at one constant post-L width

Apply `distant_links` after getting remote prerequisites
(`Outposts`, firstRadius). Then via port-geometry/certificate compare to
the actual group logarithm at that link -- no independent control
on U outside window assumed. Keep this constant throughout repeated
tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β B W : ℝ} {d : ℝ} {X : Config G f}

structure Outposts (S : StepData c f) (U : Config G f) (V : Config G c) (k : S.Choices) (x W : ℝ) (i : Site c) : Prop where
  faces j : separation i (S.ratio.parent j.1) ≤ radiusB x → Pressure.toll U j ≤ fiery G x S.patch.L
  braid j : j.1=i → wire (S.prediction U k) V j ≤ W * fiery G x S.patch.L
  frames : usable S U i k
lemma blaze {D : Patch} {ε : ℝ} (h : Beacons P D W ε x) (hT : P.Funds S T) (hh : S.patch=D) (hS : Larger (G:=G) S)
    {H K} (hk : Aff.Alongside H K T) (hF : Booth P S T) (hV : Aff.cert S x A V) (k : S.Choices) (χ : Chi) (p : RoomView A x F G) (hβ : 0<β)
    (he : 2≤radiusB x) (ht : i∉A.dome (50*radiusB x))
    (hp : Toned (2*radiusB x) i p.2 (ε*fiery G x S.patch.L/(coupling β))) :
    Outposts S (gazed T k χ V x β d p) V k x W i:= by
  let b:=radiusB x; let U:=gazed T k χ V x β d p; let t:=fiery G x S.patch.L
  have hv y (hy : separation i y≤b):= h.fires c f S T hT hh hS H K hk hF F A V k hV χ d p β hβ y
    (Aff.exclude A _ _ _ _ ht (by unfold b at hy; omega)) (hp.shift (by unfold b at hy; omega))
  refine ⟨fun j hi=> ?_,fun j hj=> (((hv i (by simp)).2.2 j hj).1).le, fun y hy=>?_⟩
  · exact (((hv (S.ratio.parent j.1) hi).2.1 j rfl).le).trans (by linarith only [show 0≤fiery G x S.patch.L from temp_nonneg _])
  let j := Pressure.plank i y
  have hq:= ((hv j ((Work.E07.separation_plank i y hy).trans he)).2.2 ((j,0):Bond c) rfl).2.1
  let u:= S.patch.frameMass S.kernel (expandAt (S.ratio.embed j) U) (k.1 j)
  change (Fintype.card S.patch.FrameTag:ℝ)*u=1 at hq
  exact pos_of_mul_pos_right (hq.symm ▸ zero_lt_one) (show (0:ℝ)≤Fintype.card S.patch.FrameTag from by positivity)

lemma distant_links (D : Patch) (P : Teller G) (W : ℝ) (hw : 0<W) :
    ∃ w : ℝ,0<w ∧ ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
      100*(1+radiusB x) ≤ c.val → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (Z : Prices G (Active A x F))
      (Y : LinkArray G (Frozen A x F)) (p : Active A x F),
      let U := Next.SectorChange.physical A F V Y (tape Z)
      (∃ k : S.Choices, Outposts S U V k x W (Aff.home S p.val.val)) → ‖tape Z p‖ < firstRadius G → ‖tape Z p‖ ≤ w*fiery G x S.patch.L := by
  obtain ⟨C,hC,h⟩ := Work.E02.answer G D.L P.j P.bind
  obtain ⟨K,δ,hK,hδ,hl⟩ := Next.Fluctuations.log_chart_cost G
  let N : ℝ := (box (macroR D)).card * (Fintype.card PlaqAxes:ℝ); have hN:0≤N:=by unfold N; positivity
  let m:=C*N+W; let w:=K*m
  have hm:0<m:=add_pos_of_nonneg_of_pos (mul_nonneg hC.le hN) hw
  refine ⟨w,mul_pos hK hm,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR D+P.j+D.J+10),
    Work.E01.fiery_le G D.L m,Work.E01.fiery_le G D.L w,(Work.E01.largeT_tendsto G D.L).eventually (gt_mem_nhds (lt_min hδ (first_pos G)))] with x hs hx hw hr c f S T hD hT he A F V Z Y p U hk hp
  obtain ⟨k,hk⟩:=hk
  let t:=fiery G x S.patch.L; let i:=p.val.val; let j:= Aff.home S i
  have hC₀ : c.val≤f.val:= by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
  have hf : 100*macroR S.patch≤ f.val:= by rw [hD]; omega
  have hv : SliceSet S F U := fun i hi => F.on_tree _ ⟨i,hi⟩
  have hU:= h c f S hT.knobs (congr_arg RG.Patch.L hD) hT.atStep hf (by omega) F U hv V i k hk.frames
  have h₁ : port S j U ≤ N*t := by
    have hh := Work.E01.port_le S U j t (temp_nonneg _) (fun i hi => hk.faces i ((Work.E01.mcharge_maps S j i hi).trans ?_))
    · unfold N; rw [← hD]; exact hh
    rw [hD]; omega
  let g := U i * (replica S.ratio V i)⁻¹
  have h₂ : G.chord g ≤ m*t:= by
    apply hU.trans
    apply (add_le_add (mul_le_mul_of_nonneg_left h₁ (‹0<C›).le) (d:=W*t) ?_).trans_eq
    · unfold m; ring
    split
    next => exact mul_nonneg (‹0<W›.le) (temp_nonneg _)
    next => exact hk.braid (j,i.2) rfl
  have hh : m*t ≤ largeT G x D.L:= by unfold t; rw [hD]; exact hx
  obtain ⟨hQ,hL⟩:=hl g (h₂.trans (hh.trans (hr.le.trans (min_le_left ..))))
  let v:= G.plog (G.mat g)
  have hy:‖v‖≤w*t := hL.trans ((mul_le_mul_of_nonneg_left h₂ hK.le).trans_eq (by unfold w; ring))
  have hi' : v∈firstBall G:= by
    apply Metric.mem_ball.mpr; rw [dist_zero_right]; apply lt_of_le_of_lt hy
    have hw : w*t ≤ largeT G x D.L:= by unfold t;rw [hD]; exact hw
    exact hw.trans_lt (hr.trans_le (min_le_right ..))
  have hV : U i=G.lieExp (tape Z p)*replica S.ratio V i:=
    (F.off_tree _ p.val).trans (freeze_regular (j:=p) ..)
  have he : G.lieExp v=G.lieExp (tape Z p):= by rw [show G.lieExp v=_ from hQ,show g=G.lieExp (tape Z p) from by unfold g; rw [hV]; group]
  rw [show tape Z p=v from (over_ball (Metric.mem_ball.mpr (by simpa using hp):tape Z p∈firstBall G)).symm.trans ((congr_arg _ he).symm.trans (over_ball hi'))]; exact hy
end YM.PhysicalNext.InteractingRank.Milk
