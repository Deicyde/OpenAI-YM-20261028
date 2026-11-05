import YM.Push.RELAY_MARK.Pi
import YM.Work.G05.Pose
import YM.Work.G06.Pose

/-!
# Population of slots

Retain the higher factor demands when changing section. Work directly with
coordinates of based and transported plaquette curvature, so that G07
(Credit), not a conjecture of pricing, applies. For a subsequent Haar
color average, even prove *finite-dimensionality of the orbit span* of
such functions (before constructing equivariant lifts).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace Pointwise
variable {G : Gauge} {d n : ℕ}

section Generation
abbrev Chip (G : Gauge) := Slot × G.ColorIndex

def build (l : List (Chip G)) : Pre G := (l.map (fun u => slotted G u.1 u.2)).prod
lemma join_build (l p : List (Chip G)) : build (l++p)=build l*build p := by simp [build]
lemma cons_build (p : Chip G) (l : List (Chip G)) : build (p::l)=slotted G p.1 p.2*build l := by simp [build]

def powered (G : Gauge) (i : ℕ) := Submodule.span ℂ {f:Pre G | ∃ l : List (Chip G), i≤l.length ∧ f=build l}
lemma base_build (l : List (Chip G)) : build l∈powered G l.length := Submodule.subset_span ⟨l,le_rfl,rfl⟩
lemma base_one (G : Gauge) : (1 : Pre G)∈powered G 0 := base_build []
lemma solo_chip (s : Slot) (i : G.ColorIndex) : slotted G s i∈powered G 1 := by simpa [build] using base_build [(s,i)] (G:=G)
lemma power_drop {i j : ℕ} (h : i≤j) : powered G j≤powered G i := Submodule.span_mono (fun _ ⟨l,hl,he⟩=>⟨l,h.trans hl,he⟩)

lemma power_prod {i j : ℕ} {f g : Pre G} (h : f∈ powered G i) (he : g∈powered G j) : f*g∈powered G (i+j) := by
  let X := powered G (i+j)
  refine Submodule.span_induction (p:=fun f _ => f*g∈X) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨l,hl,rfl⟩
    refine Submodule.span_induction (p:=fun g _ => build l*g∈X) ?_ ?_ ?_ ?_ he
    · rintro _ ⟨s,hs,rfl⟩
      rw [← join_build]
      exact power_drop (by simpa using add_le_add hl hs) (base_build _)
    · simp
    · intro p q _ _ hp hq; rw [mul_add]; exact X.add_mem hp hq
    intro s p _ hp; rw [mul_smul_comm]; exact X.smul_mem _ hp
  · simp
  · intro p q _ _ hp hq; rw [add_mul]; exact X.add_mem hp hq
  intro s p _ hp; rw [smul_mul_assoc]; exact X.smul_mem _ hp

private lemma power_finset {ι : Type*} (F : ι → Pre G) (s : Finset ι) (p : ι → ℕ) (h : ∀ i∈s, F i∈powered G (p i)) :
    ∏ i∈s,F i∈powered G (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact base_one G
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi]; exact power_prod (h i (Finset.mem_insert_self ..)) (ih fun b hb => h _ (Finset.mem_insert_of_mem hb))

private lemma power_rep {f : Pre G} (h : f∈powered G 1) (i : ℕ) : f^i ∈ powered G i := by
  induction i with
  | zero => rw [pow_zero]; exact base_one G
  | succ i ih => rw [pow_succ]; exact power_prod ih h
end Generation

section Population
open Bid

def spelledPose (B : Fin n → Slot) (P : Pose G n) : Pre G := lumin P ∘ mapped B

lemma pose_power (B : Fin n → Slot) (P : Pose G n) (h : lows P d) : spelledPose B P∈powered G d := by
  classical
  let x (i : Fin n × G.ColorIndex) := slotted G (B i.1) i.2
  let b (m : Fin n × G.ColorIndex →₀ ℕ) : Pre G := m.prod fun i k => (x i)^k
  have hx : spelledPose B P=∑ m∈P.support,P.coeff m • b m := by
    funext U
    unfold spelledPose
    dsimp only [Function.comp_apply]
    simp only [Finset.sum_apply,Pi.smul_apply,b,lumin,MvPolynomial.aeval_def,
      MvPolynomial.eval₂_eq, Finsupp.prod,Finset.prod_apply,Pi.pow_apply]; rfl
  rw [hx]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (power_drop (h m hm) ?_)
  exact power_finset (fun i=> x i^(m i)) _ _ (fun i _=> power_rep (solo_chip _ _) _)



lemma synchronize {m j : ℕ} (B : Fin n → Slot) (V : Fin m → Slot) (P : Pose G n) (s : Fin n→ Fin m)
    (h : ∀ i, V (s i)=B i) (he : lows P j) :
    ∃ p : Pose G m, lows p j ∧ spelledPose B P=spelledPose V p := by
  refine ⟨Work.G06.redirect s (fun _=>1) P,Work.G06.redirect_lows s _ _ _ he,funext fun U=>?_⟩
  unfold spelledPose; simp only [Function.comp_apply,Work.G06.redirect_lumin]; simp only [one_smul, mapped,h]; rfl

private lemma amalgamate (B : Fin n → Slot) {m} (V : Fin m → Slot) {j i} (P : Pose G n) (S : Pose G m)
    (h : lows P j) (he : lows S i) : ∃ (k : ℕ) (W : Fin k → Slot) (x y : Pose G k),
      lows x j ∧ lows y i ∧ spelledPose B P=spelledPose W x ∧ spelledPose V S=spelledPose W y := by
  let e := Fintype.equivFin (Fin n ⊕ Fin m)
  let w t := Sum.elim B V (e.symm t)
  obtain ⟨x,hx,hX⟩ := synchronize B w P (fun t=>e (Sum.inl t)) (by simp [w]) h
  obtain ⟨y,hy,hY⟩ := synchronize V w S (fun t=>e (Sum.inr t)) (by simp [w]) he
  exact ⟨_,w,x,y,hx,hy,hX,hY⟩

private lemma low_iff (G : Gauge) (n j : ℕ) (P : Pose G n) : lows P j ↔ P ∈ MvPolynomial.restrictSupport ℂ {u| j ≤ u.sum fun _ t => t} :=
  ⟨fun h => (MvPolynomial.mem_restrictSupport_iff ℂ).mpr h, fun h => (MvPolynomial.mem_restrictSupport_iff ℂ).mp h⟩

private lemma literal_slot (b : Chip G) : ∃ (k : ℕ) (B : Fin k→Slot) (Q : Pose G k),
    lows Q 1 ∧ slotted G b.1 b.2=spelledPose B Q := by
  refine ⟨1,(fun _=>b.1),MvPolynomial.X (0,b.2), Work.G05.lows_of_zero ?_,funext fun V=>?_⟩
  · simp [lumin]
  simp [spelledPose,slotted,mapped,lumin]

lemma powered_pose {f : Pre G} (h : f∈powered G d) :
    ∃ (n : ℕ) (B : Fin n → Slot) (Q : Pose G n), lows Q d ∧ f=spelledPose B Q := by
  classical
  have he (l : List (Chip G)) : ∃ (n : ℕ) (B : Fin n → Slot) (Q : Pose G n), lows Q l.length ∧ build l=spelledPose B Q := by
    induction l with
    | nil => exact ⟨0,Fin.elim0,1,(fun _ _=>Nat.zero_le _),funext fun _=> by simp [build,spelledPose,lumin]⟩
    | cons b l ih =>
      obtain ⟨m,B,P,hP,hb⟩ := literal_slot b
      obtain ⟨n,V,Q,hQ,hl⟩ := ih
      obtain ⟨k,W,x,y,hx,hy,hX,hY⟩ := amalgamate B V P Q hP hQ
      refine ⟨k,W,x*y,by simpa [add_comm] using Work.G05.lows_mul hx hy,?_⟩
      rw [cons_build,hb,hl,hX,hY]; funext U; simp [spelledPose,lumin]
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l,hl,rfl⟩ := (show ∃ l, d ≤ l.length ∧ f=build l from hf)
    obtain ⟨m,B,p,hp,H⟩ := he l; exact ⟨m,B,p,fun i hi=>hl.trans (hp _ hi),H⟩
  | zero =>
    refine ⟨0,Fin.elim0,0,by simp [lows],funext fun U=>by simp [spelledPose,lumin]⟩
  | add f g _ _ hf hg =>
    obtain ⟨m,B,P,hP,rfl⟩ := hf
    obtain ⟨n,V,Q,hQ,rfl⟩ := hg
    obtain ⟨k,W,x,y,hx,hy,hX,hY⟩ := amalgamate B V P Q hP hQ
    rw [hX,hY]
    exact ⟨k,W,x+y,(low_iff ..).2 (Submodule.add_mem _ ((low_iff ..).1 hx) ((low_iff ..).1 hy)),funext fun U=>by simp [spelledPose,lumin]⟩
  | smul c f _ hf =>
    obtain ⟨m,B,p,hp,rfl⟩ := hf
    exact ⟨m,B,c • p,(low_iff ..).2 (Submodule.smul_mem _ _ ((low_iff ..).1 hp)),funext fun U=>by simp only [Pi.smul_apply,spelledPose,lumin,comp_apply,map_smul]⟩

/- Every function represented by such a pose depends on gauge only
at the root. -/
def accord (f : Pre G) (g : G.El) : Pre G := f ∘ gauge (fun _=>g)

lemma gauge_root {f : Pre G} (h : f∈powered G d) (u : Cover → G.El) (U : CoverConfig G) :
    f (gauge u U) = accord f (u 0) U := by
  obtain ⟨n,B,P,hP,rfl⟩ := powered_pose h
  simp only [spelledPose,accord, comp_apply]; unfold mapped
  simp only [Work.G06.slot_gauge]

lemma power_cont {f : Pre G} (h : f∈powered G d) : Continuous f := by
  have hs (l : List (Chip G)) : Continuous (build l) := by
    induction l with
    | nil => exact continuous_const
    | cons p l ih =>
      rw [cons_build]; exact Continuous.mul (by unfold slotted; fun_prop) ih
  induction h using Submodule.span_induction with
  | mem f hf => obtain ⟨l,hl,rfl⟩ := (show ∃ l,d≤l.length ∧ f=build l from hf); exact hs l
  | zero => exact continuous_const
  | add f g _ _ hf hg=> exact hf.add hg
  | smul c f _ hf=> exact hf.const_smul _

lemma power_force (b : Point) (i : G.ColorIndex) : flashed b i ∈ powered G 1 := by
  rw [fsum]; refine Submodule.sum_mem _ fun a _=>?_
  unfold hereTerm; split
  · exact Submodule.sub_mem _ (solo_chip _ _) (solo_chip _ _)
  split
  · exact Submodule.neg_mem _ (Submodule.sub_mem _ (solo_chip _ _) (solo_chip _ _))
  exact Submodule.zero_mem _

end Population

section Color

def cluster (f : Pre G) := Submodule.span ℂ (range (accord f))

lemma color_chip (g : G.El) (s : Slot) (i : G.ColorIndex) : accord (slotted G s i) g ∈
    Submodule.span ℂ (range (slotted G s)) := by
  let E := EuclideanSpace.basisFun G.ColorIndex ℝ
  let Q := (EuclideanSpace.proj i).toLinearMap.comp (G.adjoint g)
  have hu : accord (slotted G s i) g=∑ j, (Q (E j):ℂ) • slotted G s j := by
    funext U; unfold accord slotted; simp only [comp_apply,Work.G06.slot_gauge,Pi.smul_apply, Finset.sum_apply]
    let v := s.eval U
    change (Q v:ℂ) = _
    nth_rw 1 [← E.sum_repr v]; simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hu]; exact Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

lemma accord_power (g : G.El) {f : Pre G} (hf : f∈powered G d) : accord f g ∈ powered G d := by
  have hv (s : Slot) (i : G.ColorIndex) : accord (slotted G s i) g∈powered G 1 := by
    have ht : Submodule.span ℂ (range (slotted G s)) ≤ powered G 1 := Submodule.span_le.mpr (fun _ ⟨a,h⟩=> by
      rw [← h]; exact solo_chip _ _)
    exact ht (color_chip g s i)
  have hl (l : List (Chip G)) : accord (build l) g∈powered G l.length := by
    induction l with
    | nil => exact base_one _
    | cons b l ih => rw [cons_build,List.length_cons,add_comm]; exact power_prod (hv b.1 b.2) ih
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l,h,rfl⟩ := (show ∃ l, d≤l.length ∧ f=build l from hf)
    exact power_drop h (hl l)
  | zero => exact Submodule.zero_mem _
  | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c _ _ hx => exact Submodule.smul_mem _ c hx

lemma cluster_finite {f : Pre G} (hf : f∈powered G d) : FiniteDimensional ℂ (cluster f) := by
  classical
  have hp {f g : Pre G} (hf : (cluster f).FG) (hg : (cluster g).FG) : (cluster (f*g)).FG :=
    (hf.mul hg).of_le (Submodule.span_le.mpr (fun _ ⟨p,h⟩ => by
      rw [← h]; exact (Submodule.mul_mem_mul (M:=cluster f) (N:=cluster g) (m:=accord f p) (n:=accord g p)
        (Submodule.subset_span ⟨p,rfl⟩) (Submodule.subset_span ⟨p,rfl⟩))))
  have ht (f : Pre G) (hf : ∀ g, accord f g=f) : (cluster f).FG := (Submodule.fg_span_singleton (R:=ℂ) f).of_le
    (Submodule.span_mono (fun _ ⟨u,h⟩ => by rw [← h,hf]; exact mem_singleton _))
  have hv (s : Slot) (i : G.ColorIndex) : (cluster (slotted G s i)).FG :=
    (Submodule.fg_span (R:=ℂ) (finite_range (slotted G s))).of_le (Submodule.span_le.mpr (fun _ ⟨u,h⟩ => by rw [← h]; exact color_chip u s i))
  have hl (l : List (Chip G)) : (cluster (build l)).FG := by
    induction l with
    | nil => exact ht 1 (fun _=>rfl)
    | cons b l ih => rw [cons_build]; exact hp (hv b.1 b.2) ih
  apply Module.Finite.of_fg
  induction hf using Submodule.span_induction with
  | mem f h=> obtain ⟨l,h,rfl⟩ := (show ∃ l, d ≤ l.length ∧ f=build l from h); exact hl l
  | zero => exact ht 0 (fun _=>rfl)
  | add f g _ _ hf hg =>
    refine (hf.sup hg).of_le (Submodule.span_le.mpr (fun _ ⟨i,h⟩=>?_))
    rw [← h]; exact Submodule.add_mem_sup (S:=cluster f) (T:=cluster g) (s:=accord f i) (t:=accord g i)
      (Submodule.subset_span ⟨i,rfl⟩) (Submodule.subset_span ⟨i,rfl⟩)
  | smul c f _ ih =>
    refine ih.of_le (Submodule.span_le.mpr (fun _ ⟨i,h⟩=>?_))
    rw [← h]; exact (cluster f).smul_mem c (Submodule.subset_span (a:=accord f i) ⟨i,rfl⟩)
end Color

section Symmetry

lemma star_power {f : Pre G} (hf : f∈powered G d) : star f∈powered G d := by
  have hw (s : Slot) (i : G.ColorIndex) : star (slotted G s i)=slotted G s i := funext (fun U=> by simp [slotted])
  have hl (l : List (Chip G)) : star (build l)=build l := by
    induction l with
    | nil => simp [build]
    | cons b l ih => rw [cons_build,star_mul,ih,hw,mul_comm]
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l,h,rfl⟩ := (show ∃ l, d≤l.length ∧ f=build l from hf)
    rw [hl]; exact power_drop h (base_build _)
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c _ _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

lemma signed_power {f : Pre G} (hf : f∈powered G d) (s : Signed) : f ∘ pull s 0∈powered G d := by
  have hv (b : Slot) (i : G.ColorIndex) : slotted G b i ∘ pull s 0 ∈powered G 1 := by
    obtain ⟨v,r,-,h⟩ := Work.G06.slot_pull (G:=G) s b
    rw [show slotted G b i ∘ pull s 0 = (r:ℂ) • slotted G v i by
      funext U; simp [slotted,h]]
    exact Submodule.smul_mem _ _ (solo_chip _ _)
  have hl (l : List (Chip G)) : build l ∘ pull s 0 ∈powered G l.length := by
    induction l with
    | nil => exact base_one _
    | cons b l ih => rw [cons_build,List.length_cons,add_comm]; exact power_prod (hv b.1 b.2) ih
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨l,h,rfl⟩ := (show ∃ l, d≤l.length ∧ f=build l from hf); exact power_drop h (hl l)
  | zero => exact Submodule.zero_mem _
  | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c _ _ hx => exact Submodule.smul_mem _ c hx
end Symmetry
end YM.Push.Mark
