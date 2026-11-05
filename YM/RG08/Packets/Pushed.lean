import YM.RG08.Packets.Torus

/-!
# Periodization of the (mixed) neutral kernel substitution
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix
open scoped Topology ENNReal

set_option autoImplicit false
variable {α β : Type} [Fintype α] [Fintype β] {L c f : Side}
    {p q r v σ τ : ℝ} {d : ℕ} {B : Packet 1 α} {T U : Kernel α β}

def second (D : Packet 1 α) : Kernel α α := fun x y=>D x (fun _=>y)

omit [Fintype α] [Fintype β] in
theorem pass_push (h : town 1 B) (ht : city L T) (hk : city L U) : town 1 (push B T (fun _ _=>U)) := by
  intro x y u
  change push B T (fun _ _ => U) (pass ((1 : Side).val • u) x)
      (fun _ => pass u y) = push B T (fun _ _ => U) x (fun _ => y)
  rw [show (1 : Side).val = 1 from rfl, one_smul]
  simp only [push]
  simp_rw [transmit_one B (fun _ => U)]
  rw [← ((Equiv.addRight (L.val • u)).prodCongr (Equiv.refl α)).tsum_eq]
  apply tsum_congr
  intro a
  change T (pass (L.val • u) a) (pass u x) * _ = _
  rw [ht]
  congr 1
  rw [← ((Equiv.addRight (L.val • u)).prodCongr (Equiv.refl α)).tsum_eq]
  apply tsum_congr
  intro v
  change B (pass (L.val • u) a) (fun _ => pass (L.val • u) v) *
      U (pass (L.val • u) v) (pass u y) = B a (fun _ => v) * U v y
  rw [hk]
  have hb : B (pass (L.val • u) a) (fun _ => pass (L.val • u) v) =
      B a (fun _ => v) := by
    simpa only [show (1 : Side).val = 1 from rfl, one_smul] using h a v (L.val • u)
  rw [hb]
omit [Fintype β] in
theorem row_bind_bill {A : Kernel β α} {Z : Kernel α β} (x y) (hA : Summable (A x)) (hZ : ∀ z, ‖Z z y‖ ≤ r) :
    bind A Z x y = ∑' u,A x u * Z u y := by
  rw [bind_apply]
  let E (u: Market α) := A x u * Z u y
  have hs : Summable E := by
    apply Summable.of_norm_bounded (hA.norm.mul_right r)
    intro z
    exact (_root_.norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (hZ z) (norm_nonneg _))
  change (∑ i : α, ∑' z : Cover, E (z, i)) = ∑' u, E u
  calc
    _ = ∑' i : α, ∑' z : Cover, E (z, i) := (tsum_fintype _).symm
    _ = ∑' u : α × Cover, E (u.2, u.1) := hs.prod_symm.tsum_prod.symm
    _ = ∑' u : Market α, E u := (Equiv.prodComm α Cover).tsum_eq E

-- generic type α₁ as well. lift version
omit [Fintype β] in
private theorem binds {γ : Type} {A : Kernel γ α} {Z : Kernel α β} (x y) (hA : Summable (A x)) (hZ : ∀ z, ‖Z z y‖ ≤ r) :
    bind A Z x y = ∑' u,A x u * Z u y := by
  rw [bind_apply]
  let E (u: Market α) := A x u * Z u y
  have hs : Summable E := by
    apply Summable.of_norm_bounded (hA.norm.mul_right r)
    intro z
    exact (_root_.norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (hZ z) (norm_nonneg _))
  change (∑ i : α, ∑' z : Cover, E (z, i)) = ∑' u, E u
  calc
    _ = ∑' i : α, ∑' z : Cover, E (z, i) := (tsum_fintype _).symm
    _ = ∑' u : α × Cover, E (u.2, u.1) := hs.prod_symm.tsum_prod.symm
    _ = ∑' u : Market α, E u := (Equiv.prodComm α Cover).tsum_eq E

 omit [Fintype β] in
theorem second_ship (hT : Atlas σ L d T q)(hU : Atlas σ L d U p)
    (hB : Folded τ B r) (hτ : 0 ≤ τ) (hr : 0 ≤ r) :
    RowCost 0 1 (swap T) (q*(L.val:ℝ)^4/(L.val:ℝ)^d) ∧
    RowCost 0 1 (second B) r ∧
    RowCost 0 L (bind (second B) U) (Fintype.card α*(r*(p/(L.val:ℝ)^d))) ∧
    second (push B T (fun _ _=> U)) = bind (swap T) (bind (second B) U) := by
  have hA : RowCost 0 1 (swap T) (q*(L.val:ℝ)^4/(L.val:ℝ)^d) := fun v k=>by
    simpa only [zero_mul, Function.swap] using (hT.col.mono hT.width) k v
  have hX : RowCost 0 1 (second B) r := by
    intro x i
    have he : ∑' y:Market α, bill (second B x y) (τ*sep x.1 y.1) ≤ ENNReal.ofReal r := by
      have hf := (identify (Market α)).symm.tsum_eq (fun w=> bill (B x w) (τ*expense x w))
      refine (Eq.trans_le ?_ (hf.le.trans (hB x)))
      congr 2; ext1 z; change bill (second B x z) _= bill (B x (fun _ : Fin 1=>z)) _
      simp [second,expense] -- Fin 1 simp
      rfl
    refine (ENNReal.tsum_le_tsum (g:=fun z:Cover=>bill (second B x (z,i)) (τ*sep x.1 z)) fun z=>?_).trans ?_
    · rw [zero_mul]; apply bill_mono le_rfl; exact mul_nonneg hτ (sep_nonneg ..)
    exact (ENNReal.tsum_comp_le_tsum_of_injective (f:=fun z=>((z,i):Market α)) (fun _ _ hz=>congr_arg Prod.fst hz) (fun v=>bill (second B x v) (τ*sep x.1 v.1))).trans he
  have hY : RowCost 0 L U (p/(L.val:ℝ)^d) := hU.row.mono hU.width
  let Z := (Fintype.card α:ℝ)*(r*(p/(L.val:ℝ)^d))
  have hp := hU.nonneg
  have hh : RowCost 0 L (bind (second B) U) Z := row_block hr (by positivity) hX hY (fun _ _ _=>by simp)
  refine ⟨hA,hX,hh,?_⟩
  funext y z
  have hy x:= bill_folded x hτ hB
  have hb (x : Market α) : ‖bind (second B) U x z‖ ≤ Z := by
    apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ Z by unfold Z; positivity)).mp
    calc
      ENNReal.ofReal ‖bind (second B) U x z‖ =
          bill (bind (second B) U x z) (0 * delta L x.1 z.1) := by
        simp [bill]
      _ ≤ ∑' w : Cover, bill (bind (second B) U x (w, z.2))
          (0 * delta L x.1 w) := ENNReal.le_tsum z.1
      _ ≤ ENNReal.ofReal Z := hh x z.2
  rw [binds y z (cost_any hA le_rfl y) hb]
  have hb (x : Market α) : bind (second B) U x z=∑'v, B x (fun _=>v)*U v z := binds x z (hy x) (fun z' => atlas_entry hU z' z)
  simp only [second, push, Function.swap]
  simp_rw [transmit_one B (fun _ => U)]
  apply tsum_congr; intro x
  exact congr_arg (T x y * ·) (hb x).symm

 omit [Fintype β] in
theorem town_hall (hc : f.val=c.val*L.val) (hT : Atlas σ L d T q) (hU : Atlas σ L d U p) (h : city L T)
    (hB : Folded τ B r) (hτ : 0 ≤ τ) (hr : 0 ≤ r)
    {M N : Matrix (Co f α) (Co c β) ℝ} {A : Matrix (Co f α) (Co f α) ℝ} (hp : Matches T M) (he : Matches U N) (ha : Matches (second B) A) :
    Matches (second (push B T (fun _ _=>U))) (M.transpose*A*N) := by
  obtain ⟨ht,hk,hj,hB'⟩:= second_ship hT hU hB hτ hr
  rw [hB',Matrix.mul_assoc]
  exact applies_bind ht hj le_rfl le_rfl (matches_back hc h hp) (applies_bind hk hU.row le_rfl hU.width ha he)

end YM.RG08.Packets
