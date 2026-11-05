import YM.UVExtension.Projection.Stage

/-! Convert deterministic lift and compare its finite readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Tree Bloch Laurent Stationary Filter Function Finset
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge}

-- uniform on both adjacent transitions. overhead only assessed pre-L.
def overhead (G : Gauge) (τ : ℝ) := coverBudget G 1 (τ/2)+coverBudget G 2 (τ/2)+coverBudget G 3 (τ/2)
lemma overhead_cases (G : Gauge) (τ : ℝ) : let a := fun n : {n:ℕ//n≠0}=> @coverBudget G n.1 ⟨n.2⟩ (τ/2)
    a ⟨1,by decide⟩ ≤ overhead G τ ∧ a ⟨2,by decide⟩≤overhead G τ ∧ a ⟨3,by decide⟩≤overhead G τ ∧ 0 < overhead G τ:=by
  have h1:=cover_one (G:=G) (n:=1) (τ/2); have h2:=cover_one (G:=G) (n:=2) (τ/2); have h3:=cover_one (G:=G) (n:=3) (τ/2)
  dsimp only [overhead]; refine ⟨?_,?_,?_,?_⟩ <;> linarith
namespace Rates
variable (P : Rates G) (M : Bed)
lemma takeAny {q : Clip} {s σ t u C A E Mz : ℝ} (h : 0<s) (hc : s≤σ) (ht : s ≤ P.grainWidth/2) (hx : M.roots.strip σ C) (hp : Floor M q 1 t u) (hb : rowPrice σ C ≤ A) (ha : P.mold*Mz *overhead G P.grainWidth≤ A) (hd : P.coil*Mz *overhead G P.grainWidth ≤ E) (x : Cube G) (hi : ‖x‖≤Mz) (hy : P.Inked x) : (P.path M x).Bounds q s A E := by
  rcases overhead_cases G P.grainWidth with ⟨h₁,h₂,h₃,-⟩
  let w:= P.grainWidth
  have hu {a:ℝ}{n:ℕ}[NeZero n] (e : Chip G n → Crates G) (hA : 0<a) (hh : coverBudget G n (w/2) ≤ overhead G w) (hI : ∀ i,(issue (blend e w a x) i).Invariant) (B : ℝ) (he : a*Mz*overhead G w ≤ B): AtomWall (issue (blend e w a x)) s B:= by
    have H:=budget_hyp e w a x (half_lt_self P.width_pos); rw [abs_of_pos hA, show w-w/2=w/2 by ring] at H
    have hz:=cover_one (G:=G) (n:=n) (w/2)
    exact AtomWall.mono ⟨H,hI⟩ ht (le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hi hA.le) hh (by linarith) (mul_nonneg hA.le ((norm_nonneg _).trans hi))) he)
  let i:= plaquette ⟨(0,1),by decide⟩
  have hC : 0≤C := (tsum_nonneg (hx i i).1).trans (hx i i).2.2
  refine build_cap M h (fun i j=>(hx i j).mono hc le_rfl) hp (le_trans (show rowPrice s C≤rowPrice σ C by unfold rowPrice; gcongr) hb) (hu Sum.inl P.coil_pos h₁ hy.two E hd).1 (hu (Sum.inr∘Sum.inl) P.mold_pos h₂ hy.three A ha).1 (hu (Sum.inr∘Sum.inr) P.mold_pos h₃ hy.four A ha).1 (fun i=> ⟨hy.two _,hy.three _,hy.four _⟩) fun i j=> ⟨?_,fun l=> ?_⟩
  · have hh:= (penny_sum (c:=P.coil) Sum.inl P.width_pos x i j none).hasSum
    change HasSum (fun k=> penny (P.evB x) i j k*1) (∑' k, penny (P.evB x) i j k*lag (P.evB x) none k) at hh
    rw [hy.normal i j none] at hh; simp_rw [mul_one] at hh; exact hh
  exact hy.normal i j (some l) ▸ (penny_sum Sum.inl P.width_pos x i j (some l) (c:=P.coil)).hasSum

lemma take {q : Clip} {s σ t u C A E : ℝ} (h : 0<s) (hc : s≤σ) (ht : s ≤ P.grainWidth/2) (hx : M.roots.strip σ C) (hp : Floor M q 1 t u) (hb : rowPrice σ C ≤ A) (ha : P.mold*overhead G P.grainWidth≤ A) (hd : P.coil*overhead G P.grainWidth ≤ E) (x : Cube G) (hi : ‖x‖≤1) (hy : P.Inked x) : (P.path M x).Bounds q s A E := by
  exact takeAny P M h hc ht hx hp hb (by simpa using ha : P.mold*1*_≤A) (by simpa using hd) x hi hy

lemma store {s a A E : ℝ} (u : Skin G 1) (v : Skin G 2) (z : Skin G 3) (R : PathData G) (q : Clip) (he : R.Bounds q s A E) (hR : R=emitBase G M (issue u) (issue v) (issue z)) (hh : P.grainWidth≤s)
    (hx : E/P.coil+A/P.mold+A/P.mold ≤ a): ∃ t : Cube G,P.path M t=R ∧ P.Inked t ∧ ‖t‖≤a:= by
  subst R
  have hp:= (show AtomWall (issue u) s E from ⟨he.two,fun _=> (he.invariant _).1⟩).mono hh le_rfl
  have hα:= (show AtomWall (issue v) s A from ⟨he.three,fun _=> (he.invariant _).2.1⟩).mono hh le_rfl
  have hβ:= (show AtomWall (issue z) s A from ⟨he.four,fun _=> (he.invariant _).2.2⟩).mono hh le_rfl
  let e2 : Chip G 1 → Crates G := Sum.inl; let e3 : Chip G 2 → Crates G:= Sum.inr ∘ Sum.inl; let e4 : Chip G 3→Crates G := Sum.inr ∘ Sum.inr
  obtain ⟨t,ht,hT,ht'⟩:=fitting e2 Sum.inl_injective P.grainWidth P.coil P.coil_pos u E hp.1
  obtain ⟨x,hX,hU,hx'⟩:=fitting e3 (Sum.inr_injective.comp Sum.inl_injective) P.grainWidth _ P.mold_pos v A hα.1
  obtain ⟨y,hY,hV,hy'⟩:=fitting e4 (Sum.inr_injective.comp Sum.inr_injective) P.grainWidth _ P.mold_pos z A hβ.1
  let f:= t+x+y
  have hb {n} [NeZero n] (l:Chip G n→Crates G)(c)(p : Skin G n)(g:Cube G)(hg : blend l P.grainWidth c g=p)(ht:∀ i,f (l i)=g (l i)): issue (blend l P.grainWidth c f)=issue p:= by
    rw [← hg]; congr 1; funext i j k; unfold blend; simp_rw [ht]
  have hc : P.evB f=issue u:= hb _ _ _ _ ht fun i=> by simp [f,hU _ (show Sum.inl i∉Set.range e3 by simp [e3,Set.mem_range]),hV _ (show Sum.inl i∉Set.range e4 by simp [e4,Set.mem_range])]
  have hd : P.ev3 f=issue v:= hb _ _ _ _ hX fun i=> by
    change t (e3 i)+ x (e3 i)+ y (e3 i)=x _; rw [hT _ (show e3 i∉Set.range e2 by simp [e2,e3,Set.mem_range]),hV _ (show e3 i∉Set.range e4 by simp [e3,e4,Set.mem_range])]; simp [e3]
  have hu : P.ev4 f=issue z:= hb _ _ _ _ hY fun i=> by
    change t (e4 i)+ x (e4 i)+ y (e4 i)=y _; rw [hT _ (show e4 i∉Set.range e2 by simp [e2,e4,Set.mem_range]),hU _ (show e4 i∉Set.range e3 by simp [e3,e4,Set.mem_range])]; simp [e4]
  refine ⟨f,by rw [path,hc,hd,hu], ⟨hdummy hc (fun i=>hp.2 i),hdummy hd hα.2,hdummy hu hβ.2,?_⟩,(norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ht' hx')) hy').trans hx)⟩
  intro i j l; rw [hc]; rcases l with _|l
  · simp only [lag,Option.elim_none,mul_one]; exact (he.loop_normal i j).1
  exact (he.loop_normal i j).2 l
where hdummy {n : ℕ} {x y : ℕ→Atom G n} (h:x=y) (he:∀ i,(y i).Invariant) i: (x i).Invariant:= h.symm ▸ he i
end Rates
end YM.UVExtension.Projection
