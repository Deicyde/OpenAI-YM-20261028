import YM.UVExtension.Free.Metric

/-! Coherent use of the chosen linear Laurent lift, even at harmonic rank deficiency. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Next.Free Craft Work.F08
open scoped Topology BigOperators Classical
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]


lemma matprod {x : ℕ→Matrix n m ℂ} {y : ℕ→ Matrix m k ℂ} (h : Arrives x) (hp : Arrives y) :
    Arrives fun i=>x i*y i := (h.pair hp).post (T:=fun P => P.1*P.2) (by fun_prop)
lemma matR {x : ℕ→Matrix n m ℝ} {y : ℕ→ Matrix m k ℝ} (h : Arrives x) (hp : Arrives y) :
    Arrives fun i=>x i*y i := (h.pair hp).post (T:=fun P => P.1*P.2) (by fun_prop)

/-- Spend a working Width possibly after shrinking. Use initially for `all` sequences, even though
some downstream bounds need only eventual. (We'll calibrate those by eventual equality.) -/
abbrev Sailing (V : ℕ→Row n m) := Stock (α:=fun _=>n) (β:=fun _=>m) (fun _ : ℕ => 1) V ∧
    ∀ p : Side, Arrives fun i=> (V i).acts p
namespace Sailing

variable {A B : ℕ→Row n m} {C : ℕ→Row m k}
lemma has {x y : ℝ} (h : Sailing A) (hx : 0<x) (he : ∀ᶠ i in atTop, (A i).strip x y) :
    ∃ Z,Received A Z x y:= acts_suffice hx he h.2
lemma hears (h : Sailing A) (p : Momentum) (hp : physical p) : Arrives fun i=>(A i).read p:=by
  obtain ⟨σ,C,hσ,hC,hq⟩:= h.1.uniform
  have he : ∀ᶠ i in atTop,(A i).strip σ C:= Eventually.of_forall fun i=> by simpa using hq i
  obtain ⟨Z,hZ⟩:= has h hσ he
  exact ⟨Z.read p,read_limit hZ he hσ hp⟩
lemma of_read (h : Stock (α:=fun _=>n) (β:=fun _=>m) (fun _ : ℕ=> (1:ℝ)) A) (hp : ∀ p∈baseCube,p≠0 → Arrives fun i=> (A i).read p) : Sailing A:= by
  obtain ⟨σ,c,hσ,hc,H⟩:= h.uniform
  have he : ∀ᶠ i in atTop,(A i).strip σ c:= Eventually.of_forall fun i=> by simpa using H i
  obtain ⟨Z,hZ⟩:= row_at_puncture he hσ hp
  exact ⟨h,fun p=>⟨_,acts_limit hZ he hσ p⟩⟩
lemma mul (h : Sailing A) (g : Sailing C) : Sailing fun i=>composeRows (A i) (C i):=by
  refine ⟨?_,fun p=>?_⟩
  · have he:= h.1.times g.1; simpa only [mul_one] using he
  exact (matR (h.2 p) (g.2 p)).copy (Eventually.of_forall fun i=> ((h.1.whole i).acts (g.1.whole i) p).symm)
omit [Fintype m] [Fintype n] in
lemma plus (h : Sailing A) (g : Sailing B) : Sailing fun i=>plusRows (A i) (B i):=
  ⟨h.1.plus g.1,fun p=> ((h.2 p).plus (g.2 p)).copy (Eventually.of_forall fun i=> ((h.1.whole i).acts_plus (g.1.whole i) p).symm)⟩
omit [Fintype m] [Fintype n] in
lemma minus (h : Sailing A) (g : Sailing B) : Sailing fun i=>minusRows (A i) (B i):= by
  refine ⟨h.1.minus g.1,fun p=> ?_⟩
  exact ((((h.2 p).pair (g.2 p)).post continuous_sub)).copy (Eventually.of_forall fun i=> ((h.1.whole i).less (g.1.whole i) p).symm)
omit [Fintype m] [Fintype n] in
lemma transpose (h : Sailing A) : Sailing fun i=>transRows (A i):=
  ⟨h.1.flipped,fun p=> ((h.2 p).post (T:=Matrix.transpose) (by fun_prop)).copy (Eventually.of_forall fun _=> (acts_trans ..).symm)⟩
omit [Fintype m] [Fintype n] in
lemma const (A : Row n m) (h : Whole A) : Sailing fun _=>A:=⟨Stock.constant A h,fun _=> Arrives.steady _⟩
omit [Fintype m] [Fintype n] in
lemma scalar (h : Sailing A) (c : ℝ) : Sailing fun i=>scaleRows c (A i) := by
  refine ⟨h.1.weight _,fun p=> ?_⟩
  exact ((h.2 p).post (T:=fun x : Matrix _ _ _ => c • x) (by fun_prop)).copy (Eventually.of_forall fun _=> (acts_scale ..).symm)

variable {r : ℕ} {W : ℕ→Row n (TypeFace (r+1))}
lemma relieving (h : Sailing W) (a:Axis) : Sailing fun i=>relief a r (W i):=by
  let Q i := relief a r (W i)
  have ht:= relief_stock h.1 a
  obtain ⟨σ,c,hσ,hc,H⟩:= ht.uniform
  have he : ∀ᶠ i in atTop,(Q i).strip σ c:= Eventually.of_forall fun i=> by simpa only [mul_one] using H i
  have hP(p: Momentum) (hv:p∈ baseCube) (hQ:q p a≠0) : Arrives fun i=>(Q i).read p:=by
    have hb:= hears h (Function.update p a 0) (real_blank hv.1 a)
    let O:Matrix n (TypeFace (r+1)) ℂ→ Matrix n (TypeFace (r+1)) ℂ→ Matrix n (TypeFace (r+1+1)) ℂ:=fun U V=> ((q p a)⁻¹ • (U-V)) * (left ℂ (r+1) a)ᵀ
    refine (((hears h p hv.1).pair hb).post (T:=fun x=> O x.1 x.2) (by unfold O; fun_prop)).copy (Eventually.of_forall ?_)
    intro i; change O ((W i).read p) _=(relief a r _).read _; unfold O
    have H := h.1.whole i; rw [read_before H a hv.1,← read_part H a hv.1,inv_smul_smul₀ hQ]
  obtain ⟨T,hT⟩:= row_all he (fun f g hf hg x y hx hy=>by
    have hz: Whole x:=⟨_,_,hσ,hx.bound⟩; have hZ: Whole y:= ⟨_,_,hσ,hy.bound⟩
    apply bank_injective hz.safe hZ.safe
    apply acts_of_cube hz.safe hZ.safe; refine renew_q x.read y.read a (fun _ p=>read_here _ hz p) (fun _ p=>read_here _ hZ p) ?_
    intro p hp hu; obtain ⟨d,hd⟩:= hP p hp hu
    exact (tendsto_nhds_unique (read_limit hx (hf.tendsto_atTop.eventually he) hσ hp.1) (hd.comp hf.tendsto_atTop)).trans
      (tendsto_nhds_unique (read_limit hy (hg.tendsto_atTop.eventually he) hσ hp.1) (hd.comp hg.tendsto_atTop)).symm)
  exact ⟨ht,fun n=> ⟨_,acts_limit hT he hσ n⟩⟩
lemma shedding (h : Sailing W) (s:Axis) : Sailing fun i=>shed s r (W i):= by
  refine of_read (A:=fun i=>shed s r (W i)) (shed_stock h.1 s) (fun p hp _ =>?_)
  exact (matprod (hears h (Function.update p s 0) (real_blank hp.1 s)) (Arrives.steady _)).copy (Eventually.of_forall fun i=> (read_shed (h.1.whole i) s hp.1).symm)
lemma fold (h : Sailing W) (l : List Axis) : Sailing fun i=> folded r (W i) l:=by
  induction l generalizing W with
  | nil => exact const 0 barren_whole
  | cons a l ih => exact plus (relieving h a) (ih (shedding h a))
omit [Fintype n] in
lemma twice {W : ℕ→Row (TypeFace 2) (TypeFace 2)} (h : Sailing W) : Sailing fun i=> Double.both (W i):= by
  have hP : Sailing fun i=> Double.wing (W i):= transpose (fold (r:=1) (transpose h) (List.finRange 4))
  have hQ : Sailing fun i=> Double.flow (W i):= mul hP (const (cobound _) (Whole.boundary _))
  have hR : Sailing fun i=> Double.top (W i):= transpose (fold (r:=2) (transpose hQ) (List.finRange 4))
  have hA : Sailing fun i=> Double.X (W i):= fold (r:=0) hR (List.finRange 4)
  exact fold (r:=1) (minus (hP) (mul (transpose (const _ (Whole.boundary 3))) hA)) (List.finRange 4)
end Sailing
end YM.UVExtension.Free
