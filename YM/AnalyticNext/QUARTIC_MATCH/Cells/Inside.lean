import YM.AnalyticNext.QUARTIC_MATCH.Cells.Detect
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Post
import YM.AnalyticNext.QUARTIC_MATCH.Residual


/-!
# Sparse-coordinate arrays of the actual tensors

Convert Ward and repetition identities to kernel identities. Don't use an abstract representation
of an auxiliary abelian theory. Colors with the adjoint action of these physical matrices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior RG Wilson Function Filter Topology Bid Tensor Joint Matrix
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : ℕ} {c : Side}

abbrev Dom (G : Gauge) (n : ℕ) (c : Side) := Tensor.T (Dir G c) ℝ n

/-- In the uses below pricing may be given directly on `single X i`; thus leave
all orientation/axis/color normalizations to be tested precisely there. -/
def sparse (x : Cell (Per c)) : G.Color →L[ℝ] Dir G c :=
    ContinuousLinearMap.pi fun i => if x=shape 1 i then ContinuousLinearMap.id ℝ G.Color else 0
lemma sparse_at (x : Cell (Per c)) (v : G.Color) (i : Body 1 c) :
    sparse x v i=if x=shape 1 i then v else 0 := by
  unfold sparse; rw [ContinuousLinearMap.pi_apply]; split <;> rfl
lemma sparse_none (x : Cell (Per c)) (v : G.Color) (h : x.2.card≠1) : sparse x v=0 := by
  funext i; rw [sparse_at, if_neg ?_]; rfl
  intro H; rw [H] at h; exact h i.2.property

def Colorwise (B : Dom G n c) := ∀ t : G.El, ∀ u, B (fun i => colors t (u i)) = B u
def Uniform (B : Dom G n c) := ∀ s : Site c, ∀ u, B (fun i => shifts 1 s (u i)) = B u
lemma monochrome (x : Cell (Per c)) (t : G.El) (v : G.Color) :
    sparse x (G.adjoint t v)=colors t (sparse x v) := by
  funext i
  change _ = G.adjoint t (sparse x v i)
  rw [sparse_at,sparse_at]; split
  · rfl
  rw [map_zero]

def entries (B : Dom G n c) (hB : Colorwise B) : ArrayC (Fin n) (Per c) (ColorPart G n) := fun X =>
    ⟨B.compContinuousLinearMap (fun i => sparse (X i)), fun t u => by
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, monochrome]; exact hB t _⟩
lemma entries_eval (B : Dom G n c) (hB : Colorwise B) X U :
    (entries B hB X).val U=B (fun i => sparse (X i) (U i)) := rfl
lemma entries_rank (B : Dom G n c) (hB : Colorwise B) (i : Fin n) : Rank (entries B hB) i 1 := by
  intro X H; apply Subtype.ext; apply ContinuousMultilinearMap.ext; intro v
  exact B.map_coord_zero i (sparse_none _ _ H)

lemma direction (F : Ink G c) : ∑ x : Cell (Per c), sparse x (F x)=F ∘ shape 1 := by
  classical
  funext i; rw [Finset.sum_apply,Finset.sum_eq_single (shape 1 i)]
  · rw [sparse_at, if_pos rfl]; rfl
  · intro x _ H; rw [sparse_at, if_neg H]
  simp

lemma pays_inputs (B : Dom G n c) (hB : Colorwise B) (F : Fin n→ Ink G c) :
    post (entries B hB) F=B (fun i => F i ∘ shape 1) := by
  conv_rhs => rw [show (fun i => F i ∘ shape 1)=(fun i => ∑ x : Cell (Per c), sparse x (F i x)) from
    funext fun i => (direction (F i)).symm]
  unfold post; simp_rw [entries_eval]
  classical
  rw [ContinuousMultilinearMap.map_sum_finset]
  rfl

lemma curl_grad (F : Ink G c) : track F ∘ shape 1 = gradient (fun i => F (i,∅)) := by
  funext b; rw [Function.comp_apply,track_shape 0]; ext j
  obtain ⟨x,i⟩ := b; obtain ⟨d,rfl⟩ := axisEquiv.surjective i
  unfold gradient; rw [show axisEquiv.symm (axisEquiv d)=d from axisEquiv.symm_apply_apply _]; exact d_sites x d (parts G 0 (F ∘ shape 0) j)

theorem entries_closed (B : Dom G n c) (hB : Colorwise B) (h : Residual.Legal B) (j : Fin n) :
    lower j (entries B hB) = 0 := by
  funext X; apply Subtype.ext; apply ContinuousMultilinearMap.ext; intro V
  rw [← post_recovers]; rw [transfers, pays_inputs]
  let W i := (Pi.single (X i) (V i) : Ink G c)
  let v (i : Fin n) : Dir G c := W i ∘ shape 1
  change B (fun i => update W j (track (W j)) i ∘ shape 1)=_
  rw [show (fun i => update W j (track (W j)) i ∘ shape 1)=update v j (track (W j) ∘ shape 1) from
    funext fun i => by by_cases hi : i=j <;> simp [v,hi], curl_grad]
  exact h.ward ..

lemma sparse_move (b : Site c) (X : Cell (Per c)) (u : G.Color) : sparse (move b X) u = shifts 1 (-b) (sparse X u) := by
  funext v
  rw [shift_one_apply,sparse_at,sparse_at]
  simp only [move,shape,Prod.ext_iff,← sub_eq_add_neg,eq_sub_iff_add_eq]

lemma entries_cohere (B : Dom G n c) (hB : Colorwise B) (h : Uniform B) : Cohere (entries B hB) := by
  intro b X; apply Subtype.ext; apply ContinuousMultilinearMap.ext; intro v
  rw [entries_eval,entries_eval]; simp_rw [Function.comp_apply, sparse_move]; exact h ..

section period
open Sheets
variable {d : Side} (h : c.val∣d.val)

lemma sparse_echo (x : Cell ℤ) (u : G.Color) [Fintype ↥(Deck h)] :
    reuses h (sparse (tor c x) u) = ∑ w : Deck h, sparse (move w.val (tor d x)) u := by
  classical
  funext i; rw [Finset.sum_apply]; change sparse _ _ _ = _
  simp_rw [sparse_at]; split_ifs with hx
  · have ht : project h i.1 = wrap c x.1 := (show (tor c x).1=(shape 1 _).1 from congr_arg Prod.fst hx).symm
    let W : Deck h := ⟨i.1-wrap d x.1,by rw [AddMonoidHom.mem_ker,map_sub, ht, Sheets.project_wrap,sub_self]⟩
    have hf w : move (w : Deck h).val (tor d x) = shape 1 i ↔ w=W := by
      constructor
      · intro H; apply Subtype.ext; exact eq_sub_of_add_eq' (congr_arg Prod.fst H)
      intro h; subst w; apply Prod.ext
      · change wrap d x.1 + (i.1-wrap d x.1)=i.1; simp
      exact (show (tor c x).2=(shape 1 ((project ‹_›) i.1,i.2)).2 from congr_arg Prod.snd hx)
    simp_rw [hf]; simp
  symm; apply Finset.sum_eq_zero
  intro w _; rw [if_neg ?_]; intro hw
  apply hx
  apply Prod.ext
  · have he : wrap d x.1 + w.val=i.1 := congr_arg Prod.fst hw
    have hu := congr_arg (project h) he
    rw [map_add,Sheets.project_wrap,show project h w.val=0 from w.property,add_zero] at hu
    exact hu
  exact (show (move w.val (tor d x)).2=(shape 1 i).2 from congr_arg Prod.snd hw)

/-- Lift-compatible inputs. -/
def Compatible (F : Dom G n d) (B : Dom G n c) := ∀ V : Fin n → Dir G c,
    F (fun i => reuses h (V i))= (Sheets.mult h : ℝ)* B V

def stripDeck (i : Fin n) : (Fin n → Deck h) ≃ ↥(upperDeck i h) × Deck h where
  toFun f := (⟨fun j => (f j).val-(f i).val,by
    refine ⟨fun j => ?_,?_⟩
    · dsimp only; rw [map_sub, show project _ _ = 0 from (f j).property, show project _ _ = 0 from (f i).property,sub_zero]
    exact sub_self _⟩, f i)
  invFun w j := w.2 + ⟨w.1.val j, w.1.property.1 j⟩
  left_inv f := funext fun j => Subtype.ext (show (f i).val+((f j).val-(f i).val)=(f j).val by abel)
  right_inv p := by
    have hx : p.1.val i=0 := p.1.property.2
    refine Prod.ext ?_ ?_
    · apply Subtype.ext; funext j; change p.2.val+p.1.val j-(p.2.val+p.1.val i)=_
      rw [hx]; abel
    exact Subtype.ext (show p.2.val+p.1.val i=p.2.val by rw [hx, add_zero])

lemma is_periodic (i : Fin n) (F : Dom G n d) (B : Dom G n c) (hC : Colorwise F) (hD : Colorwise B)
    (he : Uniform F) (hf : Compatible h F B) (X : Fin n→Cell ℤ) :
    entries B hD (tor c ∘ X)= ∑' w : ↥(upperDeck i h), entries F hC (sway w.val (tor d ∘ X)) := by
  classical
  letI := Fintype.ofFinite (Deck h)
  letI : Finite (upperDeck i h) := inferInstance
  letI := Fintype.ofFinite (upperDeck i h)
  rw [tsum_fintype]; apply Subtype.ext; apply ContinuousMultilinearMap.ext; intro v
  let J (k : ↥(upperDeck i h)) := (entries F hC (sway k.val (tor d ∘ X))).val v
  change _=((eligible G n).subtype (∑ k : ↥(upperDeck i h), entries F hC (sway k.val (tor d ∘ X)))) v
  rw [map_sum,_root_.sum_apply]
  change _ = ∑ k,J k
  have H := hf (fun i => sparse (tor c (X i)) (v i))
  -- compare on occurrence lifts rather than distinct physical coordinates only
  simp_rw [sparse_echo h] at H
  let q (m : Fin n) (k : Deck h) := sparse (move k.val (tor d (X m))) (v m)
  change F (fun i => ∑ j, q i j)=_ at H
  rw [ContinuousMultilinearMap.map_sum_finset] at H
  have hX : (∑ j : (Fin n → Deck h), F (fun i => q i (j i)))=(mult h:ℝ)*∑ i,J i := by
    rw [← Equiv.sum_comp (stripDeck h i).symm,Fintype.sum_prod_type]
    have hv (z : upperDeck i h) (t : Deck h) :
        F (fun x => q x ((stripDeck h i).symm (z,t) x)) = J z := by
      let G := entries F hC
      let X' := sway z.val (tor d ∘ X)
      have hz : G (move t.val ∘ X')=G X' := entries_cohere F hC he _ _
      apply Eq.trans ?_ (congr_arg (fun k : ColorPart _ _ => k.val v) hz)
      change _=(entries F hC _).val v; rw [entries_eval]
      apply congr_arg F; funext m; unfold q
      congr 2; change move (t.val+_) _=_
      simp only [Function.comp_apply,X',sway,move]; congr 1; abel
    simp_rw [hv, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,mult,Nat.card_eq_fintype_card]
  rw [show (Fintype.piFinset fun _ : Fin n => (Finset.univ: Finset (Deck h)))=Finset.univ by ext; simp,hX] at H
  exact (mul_left_cancel₀ (show (↑(mult h):ℝ)≠0 by exact_mod_cast (mult_pos _).ne') H).symm
end period
end YM.AnalyticNext.QuarticMatch.BoxChain
