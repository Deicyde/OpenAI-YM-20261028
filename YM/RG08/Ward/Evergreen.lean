import YM.RG08.Ward.Morning
/-!
# Produced Ward conditions on every fixed-order step, true displacements
No Ward input to contraction missed by the winding events. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Bloch Reflect
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {F : Air G} (i : G.ColorIndex) (P : Patch) (k : KernelChoices) (X : Repeated P.L)
variable (w : Train P.J) (D : ChartRatio G) (M : FreeResolvent.FaceRow) (hD : LocalRatio D)

include hD
theorem legal (h : P.Branches k G) (H : Gets F) (hu : Halt F)
    (hF : ∀ f,Faithful (quad G (YM.RG08.hessian (pink k.penalty w))) F f)
    (hM : Whole M) (hm : ∀ c,(M.acts c).IsSymm) (hb : ∀ c f (hs:f.val=c.val*P.L.val),∃ U:Matrix (Body 1 f) (Body 1 c) ℝ, Inputs (linked P k c f hs) U ((pink k.penalty w).acts f) (M.acts c)) (n) :
    Beacon n (strike i P D k X w F) (quad G (YM.RG08.hessian M)) ∧ Faithful (quad G (YM.RG08.hessian M)) (strike i P D k X w F) n := by
  let m (l:ℕ):Side:=⟨l+1,Nat.succ_pos _⟩; let s l:= m l * n
  let g (l:ℕ):Ratio (m l) (s l):=⟨n,rfl⟩
  have hm': Tendsto (fun l=> (s l).val) atTop atTop := by
    change Tendsto (fun l:ℕ=>(l+1)*n.val) atTop atTop
    refine tendsto_atTop_mono ?_ (tendsto_add_atTop_nat 1)
    intro i; change i+1≤ _; exact Nat.le_mul_of_pos_right _ n.property
  let K:=YM.RG08.hessian M; let V l : Air G := Reflect.veil P k X w i D (some (s l)) F
  have ht l:= hb (s l) (s l*P.L) rfl
  have ht' l:= accepted P k X w i D hD h rfl M hM hm (ht l).choose (ht l).choose_spec H hu (hF _)
  let Q:=quad G K
  have hh:= (conditional_truth G X k w h).1
  have hc: Whole (coarseMean G X k w) := (hh.prod (probe_recites G P k|>.1.flipped)).weight _
  obtain ⟨hy,hO⟩:=WarmExhale hh hc (Gets_awake P D k i H)
  obtain ⟨hp,hQ,hv⟩:=price_stanza G hM hm n
  let F':= strike i P D k X w F
  have hz : Beacon n F' Q:= fashions Q (fun _=>Q) (V:=V) (hO s hm') (Mending.one Q hQ) n (fun l=> tilt_beacon (g l) G (V l) (fun i j=> ((ht' l).2.1 i j).1) Q hp.1 (ht' l).2.2.1)
  let hh' := opines_true (excise_beacons Q F' hz) (excise_below (p:=F') hy.1) (excise_heap F') (fun i j=>by unfold excise; split_ifs; apply Tunable.zero; exact (hy.2 i j).1) hp
  refine ⟨hz,fun q n=>?_⟩; obtain ⟨f,h,hv⟩:= hh' q n; refine ⟨_,h,fun j hj=>?_⟩
  rw [hv j hj]; congr 1
end YM.RG08
