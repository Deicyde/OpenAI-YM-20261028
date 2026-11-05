import YM.Next.RANK.Lens

/-! Right solution and identifying stencils -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice Wilson CellsInt Maxwell Labels Tensor Function Finset Configuration Submodule
open scoped Classical Topology BigOperators

variable {G : Gauge} {d n k : ℕ}

def iris (d k : ℕ) (G : Gauge) : (Shelf G d k→ℝ) →ₗ[ℝ] Horizon G where
  toFun := piano G d k
  map_add' x y := by simp only [piano,Pi.add_apply, add_smul,sum_add_distrib]
  map_smul' r x := by simp only [piano,Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,Finset.smul_sum]
lemma specific (d k : ℕ) : Injective ((focus (d:=d) k).comp (iris d k G)) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.2 fun i hi => keyboard G d k i hi)

-- span of observed jets through d recover all secure readings at this d
lemma typist (h : n+2≤d) (k : ℕ) (hk : k ≤ n) (A : Taylor G n) : ∃ v : Shelf G d k → ℝ, iris d k G v=sweep n A := by
  let w (p : Fin (Labels.dim G n)) := (axes G n).repr A p • Pi.single (fan p h hk) (1:ℝ)
  refine ⟨∑ p,w p,?_⟩
  have hc p : iris d k G (w p)=(sweep n) ((axes G n).repr A p • axes G n p) := by
    unfold w; rw [map_smul,map_smul]; congr 1; unfold iris piano
    simp only [LinearMap.coe_mk,AddHom.coe_mk, Pi.single_apply,ite_smul,zero_smul,one_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; rfl
  rw [map_sum]; simp_rw [hc]; rw [← map_sum]; simp

private def embedKey (h : d≤k) (i : Shelf G d 0) : Shelf G k 0 := ⟨⟨i.val.val,i.val.property.trans h⟩,Nat.zero_le _⟩
private lemma dup (h : d ≤ k) (v : Shelf G d 0 → ℝ) : ∃ w : Shelf G k 0 → ℝ,
    piano G k 0 w=piano G d 0 v := by
  let f := embedKey (G:=G) h
  let w := ∑ i : Shelf G d 0, v i • Pi.single (f i) (1:ℝ)
  have he i : iris k 0 G (Pi.single (f i) 1)=tester i.val.val := by
    unfold iris piano; simp only [LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply,ite_smul,one_smul,zero_smul,sum_ite_eq', Finset.mem_univ,↓reduceIte]; rfl
  refine ⟨w,?_⟩; change iris k 0 G w=_; dsimp only [w]; rw [map_sum]; simp_rw [map_smul,he]; rfl

lemma daylight (d : ℕ) (f : Horizon G) (h : shutter f) : ∃ v, focus (d:=d) 0 f=focus (d:=d) 0 (iris d 0 G v) := by
  induction d using Nat.twoStepInduction generalizing f with
  | zero =>
    refine ⟨0,?_⟩; funext i; have hv := i.property; omega
  | one =>
    refine ⟨0,?_⟩; funext i; have hv := i.property; omega
  | more n _ H =>
    obtain ⟨A,hA⟩ := lens n f h
    obtain ⟨x,hx⟩ := typist (d:=n+2) le_rfl 0 (Nat.zero_le _) A
    have hb : shutter (f-(sweep n) A) := (signal G).sub_mem h (shutters _)
    obtain ⟨v,hv⟩ := H _ hb
    obtain ⟨w,hw⟩ := dup (Nat.le_succ (n+1)) v
    change iris (n+2) 0 G w=iris (n+1) 0 G v at hw
    refine ⟨w+x,?_⟩; rw [map_add,hw,hx,map_add]
    ext1 i; rcases i with ⟨L,h₁,h₂,h₃⟩
    by_cases hp : L.degree=n
    · have hZ : gesture L (iris (n+1) 0 G v)=0 := by
        unfold iris piano; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum]
        refine sum_eq_zero fun i _ => ?_; rw [map_smul,tester,gesture_over L ?_,smul_zero]
        have hz := i.val.property; unfold generation at hz; omega
      change gesture L f=gesture L _+gesture L _; rw [hA _ hp h₁,hZ,zero_add]
    have hp' : L.degree+2 ≤ n+1 := by omega
    have hh : gesture L (f-(sweep n) A)=gesture L (iris (n+1) 0 G v) := congr_fun hv ⟨L,h₁,h₂,hp'⟩
    rw [map_sub] at hh; exact sub_eq_iff_eq_add.mp hh

-- filter any smaller k on same coefficients. Thus invertibility on restricted ν (injective) gives universal stencils using at least order k.
private def root (i : Shelf G d k) : Shelf G d 0 := ⟨i.val,Nat.zero_le _⟩
private lemma root_scale (v : Shelf G d 0 → ℝ) (k) :
    focus (d:=d) k (iris d 0 G v)=focus (d:=d) k (iris d k G (fun i => v (root i))) := by
  funext i; rcases i with ⟨L,h₁,h₂,h₃⟩; change gesture L _=gesture L _
  unfold iris piano; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum,map_sum]
  symm
  change (∑ i : Shelf G d k, gesture L (v (root i) • tester (root i).val.val)) = _
  rw [← sum_image (g:=root (G:=G) (k:=k) (d:=d)) (s:=univ) (f:=fun i => gesture L (v i • tester i.val.val)) (by intro i _ j _ h; exact Subtype.ext (congr_arg (Subtype.val : Shelf G d 0 → _) h))]
  refine sum_subset (subset_univ _) ?_; intro i _ hi
  rw [map_smul,tester,gesture_over L ?_,smul_zero]
  have hc : ¬ k ≤ i.val.val.1 := fun H => hi (mem_image.mpr ⟨⟨i.val,H⟩,mem_univ _,Subtype.ext rfl⟩)
  omega

private def solution (d k : ℕ) := ((focus (d:=d) k).comp (iris d k G)).leftInverse
private lemma gloss (d k : ℕ) (v) : solution (G:=G) d k (focus k (iris d k G v))=v := LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (specific _ _)) v
private lemma exists_root (f : Horizon G) (v) (h : focus (d:=d) 0 f=focus (d:=d) 0 (iris d 0 G v)) (k : ℕ) (X : Shelf G d k) :
    solution d k (focus k f) X=v (root X) := by
  have he : focus (d:=d) k f=focus (d:=d) k (iris d 0 G v) := by funext j; exact congr_fun h (⟨j.val,j.property.1,Nat.zero_le _,j.property.2.2⟩ : Hub G d 0)
  rw [he,root_scale v,gloss]

/-- coefficients even for nonsecure input. -/

def predicts (i : KeyIn G d) : Horizon G →ₗ[ℝ] ℝ :=
    let s := i.val.1
    (LinearMap.proj ⟨i,le_rfl⟩).comp ((solution d s).comp (focus s))
lemma predicts_sensor (f : Horizon G) (v) (h : focus (d:=d) 0 f=focus (d:=d) 0 (iris d 0 G v)) (i : KeyIn G d) : predicts i f=v ⟨i,Nat.zero_le _⟩ := exists_root f v h i.val.1 ⟨i,le_rfl⟩

def glimpse (u : KeyIn G d) (p : Hub G d u.val.1) : ℝ := solution d u.val.1 (Pi.single p (1:ℝ)) (⟨u,le_rfl⟩ : Shelf G d u.val.1)

lemma concentrates (u : KeyIn G d) (f : Horizon G) : predicts u f=∑ i, gesture i.val f * glimpse u i := by
  let a:=u.val.1; let H := Hub G d a
  have he : focus a f=∑ i : H, gesture i.val f • Pi.single i 1 := by
    ext1 i; simp [Pi.single_apply,H]; rfl
  change solution d a (focus a f) _=_
  rw [he, map_sum,Finset.sum_apply]; simp_rw [map_smul]; rfl

def cloud (d : ℕ) (f : Horizon G) : Horizon G := ∑ i : KeyIn G d,predicts i f • tester i.val
lemma visible (d : ℕ) (f : Horizon G) (h : shutter f) : focus (d:=d) 0 (cloud d f)=focus (d:=d) 0 f := by
  obtain ⟨v,hv⟩ := daylight d f h
  have he : cloud d f=iris d 0 G v := by
    unfold cloud iris piano; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [predicts_sensor f v hv]
    let hT : KeyIn G d ≃ Shelf G d 0 := ⟨fun i => ⟨i,Nat.zero_le _⟩, Subtype.val,fun _ => rfl,fun _ => rfl⟩
    exact Fintype.sum_equiv hT _ _ (fun i => rfl)
  rw [he,hv]

lemma forecast (i j : KeyIn G d) : predicts i (tester j.val)=if i=j then 1 else 0 := by
  let s : Shelf G d 0 := ⟨j,Nat.zero_le _⟩
  let v : Shelf G d 0 → ℝ := Pi.single s 1
  have hv : iris d 0 G v=tester j.val := by
    unfold iris piano v; simp only [LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply,ite_smul,zero_smul,one_smul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]; rfl
  rw [predicts_sensor _ v (by rw [hv]), show v _ = if (⟨i,Nat.zero_le _⟩ : Shelf G d 0) = s then (1:ℝ) else 0 from Pi.single_apply ..]
  simp only [s,Subtype.mk.injEq]
end YM.Next.Rank.Beamer
