import YM.Pert.Align.Atom
import YM.Maxwell.Bilinear
/-! Reordering jets only on the separated germ. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Nesting
open Maxwell YM.Next.Rank.Radian Function Set Filter Topology Tensor
open scoped ContDiff Classical BigOperators
variable {f g : E4→ℝ}

def Clean (f : E4→ℝ) := ∀ x : E4, x≠0 → ContDiffAt ℝ ∞ f x
lemma clean_green : Clean Green := fun _=>freeSmooth
lemma clean_chart (i j a b) : Clean (bareCurl i j a b) := fun _ hx=>Maxwell.Bare.curl_diff hx _ _ _ _
lemma clean_stream (a : List Axis) (h : Clean f) : Clean (dV a f) := fun x hx=>stroll a (h _ hx)
lemma clean_perm (hf : Clean f) {a b : List Axis} (h : List.Perm a b) : EqOn (dV a f) (dV b f) away := by
  intro x hx
  induction h generalizing x with
  | nil => rfl
  | cons c h ih => change grad c _ x=grad c _ x; exact Analysis.GermD (u:=basis c) (outside_eq _ _ (fun u hu=>ih (x:=u) hu) hx)
  | swap a b l => show grad b (grad a _) _ = grad a (grad b _) _; exact grad_comm ((clean_stream l hf x hx).of_le (WithTop.coe_le_coe.mpr le_top)) _ _
  | trans _ _ ih I => exact (ih hx).trans (I hx)
lemma clean_sub (D : List Axis) (hf : Clean f) (hg : Clean g) {x : E4} (hx : x≠0) : dV D (fun t : E4=> f t - g t) x = dV D f x - dV D g x := strolling D hf hg hx
@[simp] lemma clean_zero (D : List Axis) : dV D (0:E4→ℝ) = 0 := by induction D <;> simp_all [dV,List.foldr_cons,grad] <;> funext i <;> simp [Analysis.D] <;> rfl
lemma plain_coeff {k : ℕ} (A : Fin k → Axis) (hf : Clean f) {x : E4} (hx : x≠0) : coeff f k x (basis ∘ A) = (k.factorial : ℝ)⁻¹ * dV (List.ofFn A).reverse f x := by rw [dVcoeff k A hf hx]; change _= (_⁻¹ * ((_ : ℝ) * _)); rw [←mul_assoc,inv_mul_cancel₀ (show _ ≠0 by positivity),one_mul]
lemma stack_coeff {j k : ℕ} (A : Fin j→Axis) (B : Fin k → Axis) (hf : Clean f) {x : E4} (hx : x≠0) : coeff (fun y=> coeff f j y (basis∘A)) k x (basis ∘ B) = ((j.factorial:ℝ)⁻¹ *(k.factorial : ℝ)⁻¹) * dV (List.ofFn A ++ List.ofFn B) f x := by
  let q : ℝ := (j.factorial:ℝ)⁻¹; let a:= (List.ofFn A); let b:=List.ofFn B; let g:= dV a.reverse f
  have hg := clean_stream a.reverse hf
  have hw := ((List.perm_append_comm (l₁:=b.reverse) (l₂:=a.reverse)) |>.trans ((List.reverse_perm a).append (List.reverse_perm b)))
  change _ = (q*((_:ℝ)⁻¹))*dV (a++b) f _
  rw [←clean_perm hf hw hx, show dV (b.reverse++a.reverse) f = dV b.reverse g from List.foldr_append, dVcoeff k B hg hx]
  have hs : (fun y : E4=>coeff f j y (basis∘A)) =ᶠ[𝓝 x] (q • g) := outside_eq _ _ (fun u hu => plain_coeff A hf hu) hx
  rw [Tensor.GermCoeff k hs,Tensor.coeff_smul q ((hg x hx).of_le (WithTop.coe_le_coe.mpr le_top))]
  change q * _ = q * _⁻¹ * (_ * _); field_simp; rfl

def tagged (q v : List Axis) (x : E4) := dV (q++v) Green x
lemma extract (D S : List Axis) (a b : Axis) {x:E4} (hx : x≠0) : dV (D++S) (grad a (grad b Green)) x = tagged (D++[a]) (S++[b]) x := by
  rw [← show dV (D++S++[a,b]) Green = dV (D++S) (grad a (grad b Green)) from List.foldr_append]
  unfold tagged
  apply clean_perm clean_green _ hx
  simp only [List.append_assoc, List.cons_append,List.nil_append]
  exact (List.perm_middle (l₁:=S) (a:=a) (l₂:=[b])).append_left D -- check order
lemma bare (D S : List Axis) (i j a b : Axis) (x : E4) (hx : x≠0) : dV (D++S) (Maxwell.bareCurl i j a b) x =
    ((if a=j then tagged (D++[i]) (S++[b]) x else 0) - (if b=j then tagged (D++[i]) (S++[a]) x else 0)) -
    ((if a=i then tagged (D++[j]) (S++[b]) x else 0) - (if b=i then tagged (D++[j]) (S++[a]) x else 0)) := by
  let V:=D++S
  have hg (i j) (u:E4) (hu : u≠0) : grad i (curlOpp j a b) u = ((if a = j then grad i (grad b Green) else 0) - (if b = j then grad i (grad a Green) else 0)) u := by
    rw [Maxwell.Bare.opp_grad hu]; split_ifs<;>rfl
  have ht (f g i j : Axis) : Clean (if i=j then (grad f (grad g Green)) else 0) := fun x hx=>by split; apply HessSmooth hx; exact contDiffAt_const
  have hG (i j) : dV V (grad i (curlOpp j a b)) x = _ := ((crushed V (outside_eq _ _ (fun y hy=> hg i j y hy) hx)).eq_of_nhds.trans (clean_sub V (ht i b a j) (ht i a b j) hx))
  rw [bareCurl,←show _ = _++_ from (rfl : V=D++S), show dV V (grad i (curlOpp j a b) - grad j (curlOpp i a b)) x=_ from clean_sub V (f:=grad i (curlOpp j a b)) (g:=_)  ?_ ?_ hx, hG i j,hG j i]
  · split_ifs <;> try simp only [clean_zero,Pi.zero_apply] <;> first|simp only [V, extract _ _ _ _ hx]|rfl
    dsimp [V]; simp only [extract _ _ _ _ hx]
  all_goals exact fun u hu=> grad_smooth _ (Maxwell.Bare.opp_diff hu _ _ _) (show ((∞:ℕ∞ω)+1)≤∞ by simp)

end YM.Pert.Nesting
