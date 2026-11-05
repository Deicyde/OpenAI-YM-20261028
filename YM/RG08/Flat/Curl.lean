import YM.RG08.Flat.World

/-!
# Resolve Sigils, displaying the literal quadratic coefficient of the action
on potential links (not on the undetermined portion of `Bed.metric`).
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior Set
open scoped Topology ENNReal

set_option autoImplicit false
abbrev Links := TypeFace 1

def writ (K : Packet 1 Faces) : Kernel Links Links :=
   Pert.Bulk.bind (swap (plain (cobound 1))) (Pert.Bulk.bind (second K) (plain (cobound 1)))

def output (H : Bed) := writ (saddle H.metric)
variable {α β : Type} {T U : Kernel α β} {σ p v q : ℝ} {L : Side}

theorem recoup {s t: ℕ → Side} (hs : Tendsto (fun n=>(s n).val) atTop atTop)
    (h : RowCost σ L T p) (hσ:0 ≤ σ) (x:Market α) (y:Market β)
    {M : ∀ n, Matrix (Co (t n) α) (Co (s n) β) ℝ} (hM : ∀ n, Matches T (M n)) :
    Tendsto (fun n=> M n (wrap (t n) x.1,x.2) (wrap (s n) y.1,y.2)) atTop (𝓝 (T x y)) := by
  classical
  let f n (v:Cover) := if wrap (s n) v = wrap (s n) y.1 then T x (v,y.2) else 0
  let g (v:Cover) := if y.1=v then T x y else 0
  have he (v : Cover) : Tendsto (fun n=> f n v) atTop (𝓝 (g v)) := by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [eventually_unfold s hs y.1,eventually_unfold s hs v] with n hx hv
    by_cases e : y.1=v
    · unfold f g; rw [if_pos (by rw [e]), if_pos e]; rw [← e]
    unfold f g; rw [if_neg (by intro he; apply e; rw [← hv, he, hx])] -- hx/hv reversed?
    rw [if_neg e]
  let D (v:Cover) := ‖T x (v,y.2)‖
  have hu : Summable D := (summable_from_receipt (f:=fun v:Cover=>T x (v,y.2)) (fun v=>mul_nonneg hσ (delta_nonneg L x.1 v)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h x y.2))).norm
  have hb (n : ℕ) (v : Cover) : ‖f n v‖ ≤ D v := by
    unfold f D
    split
    · rfl
    rw [norm_zero]; exact norm_nonneg _
  have hf:= tendsto_tsum_of_dominated_convergence hu he (Eventually.of_forall hb)
  convert hf using 1
  · funext n; exact (hM ..).symm
  have ht : ∑' k,g k=T x y := tsum_ite_eq' y.1 (fun _=>T x y)
  rw [ht]

theorem readahead {s t: ℕ → Side} (hs : Tendsto (fun n=>(s n).val) atTop atTop)
    (h : RowCost σ L T p) (hU : RowCost v L U q) (hσ:0 ≤ σ) (hv : 0 ≤ v)
    {M : ∀ n, Matrix (Co (t n) α) (Co (s n) β) ℝ} (hM : ∀ n, Matches T (M n)) (ht : ∀ n, Matches U (M n)) : T=U := by
  funext x y; exact tendsto_nhds_unique (recoup (t:=t) hs h hσ x y hM) (recoup (t:=t) hs hU hv x y ht)

theorem second_row [Fintype α] {B : Packet 1 α} (hB : Folded σ B p) : RowCost σ 1 (second B) p := by
  intro v i
  have he x: ∑' y:Market α, bill (second B x y) (σ*sep x.1 y.1) ≤ ENNReal.ofReal p := by
    have hf := (identify (Market α)).symm.tsum_eq (fun w=> bill (B x w) (σ*expense x w))
    refine (Eq.trans_le ?_ (hf.le.trans (hB x))); apply tsum_congr; intro z
    change bill (second B x z) _= bill (B x (fun _=>z)) _
    simp [second,expense]; rfl
  simp_rw [delta_one]
  exact (ENNReal.tsum_comp_le_tsum_of_injective (f:=fun z=>((z,i):Market α)) (fun _ _ hz=>congr_arg Prod.fst hz) (fun w=>bill (second B v w) (σ*sep v.1 w.1))).trans (he v)

private def lineA : ℝ := Classical.choose (Work.F06.strip_of_fin Exterior.support (cobound 1) (certified 1) 1)
theorem lineA_props : 0 ≤ lineA ∧ (cobound 1).strip 1 lineA := Classical.choose_spec (Work.F06.strip_of_fin Exterior.support (cobound 1) (certified 1) 1)

def sumToken : ℝ := (Fintype.card Faces:ℝ)^2 * lineA^2

theorem sumToken_pos : 0 ≤ sumToken := by unfold sumToken; positivity

theorem sigil_row {B : Packet 1 Faces} (hB : Folded σ B p) (hs:0≤σ)(ha:σ≤1)(hp:0≤p) : RowCost σ 1 (writ B) (sumToken*p) := by
  obtain ⟨H,ht,hq⟩: 0 ≤ lineA ∧ RowCost σ 1 (plain (cobound 1)) lineA ∧ ColCost σ 1 (plain (cobound 1)) lineA := ⟨lineA_props.1,plain0 lineA_props.2 ha⟩
  have hδ (x y z:Cover): σ*delta (1:Side) x z ≤ σ*delta 1 x y + σ*delta 1 y z:= by simp_rw [delta_one,← mul_add]; exact mul_le_mul_of_nonneg_left (sep_triangle ..) hs
  have hx := row_block hp H (second_row hB) ht hδ
  have hA : RowCost σ 1 (swap (plain (cobound 1))) lineA := by intro x i; simpa only [delta_one,sep_comm x.1,swap] using hq i x
  convert row_block H (by positivity) hA hx hδ using 1
  · rfl
  unfold sumToken; ring

private theorem travel {B : Packet 1 Faces} (n : Side) (X : Matrix (Body 1 n) (Body 1 n) ℝ) (h : Sigil B n X) (he : Folded σ B p) (hp : 0 ≤ p) (hσ : 0 ≤ σ) (hv : σ ≤ 1) : Matches (writ B) X := by
  obtain ⟨A,H,h⟩:=h
  obtain ⟨H',ht,hq⟩: 0 ≤ lineA ∧ RowCost σ 1 (plain (cobound 1)) lineA ∧ ColCost σ 1 (plain (cobound 1)) lineA := ⟨lineA_props.1,plain0 lineA_props.2 hv⟩
  have hD : Matches (plain (cobound 1)) (Exterior.d 1 n):=matches_plain _
  have hδ (x y z:Cover): σ*delta (1:Side) x z ≤ σ*delta 1 x y + σ*delta 1 y z:= by simp_rw [delta_one,← mul_add]; exact mul_le_mul_of_nonneg_left (sep_triangle ..) hσ
  have hx := row_block hp H' (second_row he) ht hδ
  have hA : RowCost σ 1 (swap (plain (cobound 1))) lineA := by intro x i; simpa only [delta_one,sep_comm x.1,swap] using hq i x
  rw [← h,Matrix.mul_assoc]
  exact applies_bind hA hx hσ hσ (matches_back (by simp) (pass_one (cobound 1)) hD) (applies_bind (second_row he) ht hσ hσ H hD)

theorem output_cost {Y : Bed} (h : Y.metric.strip σ p) (hp : 0 ≤ p) (hs : 0 ≤ σ) (he : σ ≤ 1) : RowCost σ 1 (output Y) (sumToken*(Fintype.card Faces*p)) ∧ ∀ n, Matches (output Y) (quadratic Y n) :=
  ⟨sigil_row (settled h) hs he (by positivity),fun n=>Flat.travel n (quadratic Y n) ⟨_,matches_plain _,rfl⟩ (settled h) (by positivity) hs he⟩

theorem subtract_row (h : RowCost σ L T p) (h' : RowCost σ L U q) (hp:0≤p) (hq:0≤q) : RowCost σ L (fun x y=> T x y-U x y) (p+q) := by
  intro x y
  rw [ENNReal.ofReal_add hp hq]
  refine (ENNReal.tsum_le_tsum fun z=> (bill_sub (T x (z,y)) (U x (z,y)) (σ*delta L x.1 z))).trans ?_
  rw [ENNReal.tsum_add]
  exact add_le_add (h _ _) (h' _ _)

variable {Y H : Bed} {K : Packet 1 Faces}

theorem resolve {s : ℕ→Side} (hs:Tendsto (fun i=>(s i).val) atTop atTop) (ht:∀ i, Sigil K (s i) (quadratic Y (s i)-quadratic H (s i)))
    {ε C : ℝ} (he : Y.metric.strip σ p)(hg:H.metric.strip σ p) (hp:0≤p)(hσ:0≤σ)(h₀:σ≤1)
    (h : Folded ε K C) (hε:0≤ε)(hv:ε≤1)(hC:0≤C) :
    (fun x y=> output Y x y - output H x y)=writ K ∧ RowCost ε 1 (fun x y=> output Y x y - output H x y) (sumToken*C) := by
  obtain ⟨hq,H₁⟩:=output_cost he hp hσ h₀
  obtain ⟨hr,H₂⟩:=output_cost hg hp hσ h₀
  let k : Kernel Links Links:= fun x y=> output Y x y-output H x y
  have hM i : Matches k (quadratic Y (s i)-quadratic H (s i)) := by
    intro x y
    have h:= display_sub (A:=output Y) (B:=output H) x y (cost_any hq hσ x) (cost_any hr hσ x)
    exact h.trans <| congr_arg₂ (fun a b:ℝ=>a-b) (H₁ _ x y) (H₂ _ x y)
  have hP : 0 ≤ sumToken*(Fintype.card Faces*p):=mul_nonneg sumToken_pos (by positivity)
  have hX := sigil_row h hε hv hC
  have hQ : k=writ K := readahead (T:=k) (t:=s) hs (subtract_row hq hr hP hP) hX hσ hε hM (fun i=> Flat.travel _ _ (ht i) h hC hε hv)
  exact ⟨hQ,(show RowCost ε 1 k _ by rw [hQ]; exact hX)⟩
end YM.RG08.Flat
