import YM.RG08.Germ.Stalk

/-!
# Transport of all strict contributions across a Wilson step

`frequency` pre-block multiplier; every component control on own mesh.
Row mean stability post-block as in Report. The line exposures charge y
which can include finescale delay.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G : Gauge} {w A : ℝ} {r e i j : ℕ}

-- eta possibly VERY SMALL.
lemma lump_sum (ν : G.ColorIndex) (P : Patch) (D : ChartRatio G) (k : KernelChoices) (hw : 0≤w) :
    ∃ C : ℝ,0≤C ∧ Glow (luggage ν P D k i j) w C := by
  obtain ⟨A,hA,H⟩:= blot_pays P ν k.penalty hw (r:=j)
  let β := ((j+1:ℕ):ℝ)*w; have hv : 0 ≤ β := by unfold β; positivity
  obtain ⟨B,hB,hP⟩:= brim_price ν D hv j
  let F := gemL P.L (brimJ ν D j)
  have hf : β ≤ P.L.val * β := le_mul_of_one_le_left hv (by exact_mod_cast P.L.property)
  have hx := gem_price (brimJ ν D j) hP hw hf
  let C := (Fintype.card (Park G P.L):ℝ)^j *((P.L.val:ℝ)^4*(Real.exp (4*β)^j*B)); have hC : 0 ≤ C:= Charge.nonneg hx
  refine ⟨A+C,add_nonneg hA hC,(Charge.neg ?_).add ?_ (fun i=> (ling_pos _ _).le)⟩ -- expected motive issues
  · split; exact H; exact glow_less (Charge.zero _) le_rfl hA
  split; exact hx; exact glow_less (Charge.zero _) le_rfl hC
-- post menu. small-width inputs can use width exactly 1.
def tariffTok (ν : G.ColorIndex) (P : Patch) (D : ChartRatio G) (k : KernelChoices) (e r : ℕ) :=
    (lump_sum ν P D k (i:=e) (j:=r) zero_le_one).choose
lemma tariff_yes (ν : G.ColorIndex) (P : Patch) (D : ChartRatio G) (k : KernelChoices) (e r : ℕ) (h : w≤1) :
    Glow (luggage ν P D k e r) w (tariffTok ν P D k e r) := glow_less (lump_sum ν P D k (i:=e) (j:=r) zero_le_one|>.choose_spec.2) h le_rfl
variable {I : Type} {P : I→Patch} {L : I→Side} {v δ η σ : I→ℝ} {y : I→ℝ}
    {F V : I → Pot G j} {M Q : ∀ i, Row (Fink G (L i)) (Fink G (L i))} {B T : ∀ i,Row (Fink G (L i)) (Loc G 1)}

lemma fiscal_lot (hp : Weighed y (fun i => ((L i).val:ℝ))) (hu : Audience y) : Weighed y (fun i=> (Fintype.card (Park G (L i)):ℝ)) := by
  let K : ℝ := Fintype.card (Loc G 1)
  have he (i) : (Fintype.card (Park G (L i)):ℝ)=((L i).val:ℝ)^4*K+K := by unfold Park Fink Co K; rw [Fintype.card_sum, Fintype.card_prod,site_card]; push_cast; rfl
  simp_rw [he]; have hx : Weighed y (fun _=>K) := Weighed.constant y (Nat.cast_nonneg _)
  exact ((hp.powers 4).times hx).plus hx hu
lemma gem_obeys (j : ℕ) (hp : Weighed y (fun i=> ((L i).val:ℝ))) (hu : Audience y)
    (h : 0 ≤ v) (hq : v ≤ 1) (hf : ∀ i, (j+1:ℕ) • v i ≤ (L i).val*σ i) {F : I → Pot G j} (hk : Voucher y δ F σ) : Voucher y δ (fun i=> gemL (L i) (F i)) v := by
  obtain ⟨W,hW,H⟩:=hk
  have hD : Weighed y (fun i=> Real.exp (4*((j+1:ℕ) • v i))) := by
    apply (Weighed.constant y (Real.exp_pos (4*((j+1:ℕ) • (1:ℝ)))|>.le)).mono (fun i=> (Real.exp_pos _).le)
    intro i; apply Real.exp_monotone; gcongr; exact hq i
  refine ⟨_,((fiscal_lot (G:=G) hp hu).powers j).times ((hp.powers 4).times ((hD.powers j).times hW)), fun i=>?_⟩
  apply glow_less (gem_price _ (H i) (h i) (by simpa only [← nsmul_eq_mul] using hf i)) le_rfl
  exact le_of_eq (by simp only [Pi.mul_apply, nsmul_eq_mul]; ring)
lemma gem_accrue (j : ℕ) (hp : Weighed y (fun i=> ((L i).val:ℝ))) (hu : Audience y)
    (h : 0 ≤ v) (hq : v ≤ 1) (hv : 0 ≤ σ) (hf : ∀ i, (j+1:ℕ) • v i ≤ (L i).val*σ i) {F H : I → Pot G j}
    (hk : Both y δ F H σ) : Both y δ (fun i=> gemL (L i) (F i)) (fun i=> gemL (L i) (H i)) v := by
  refine ⟨gem_obeys j hp hu h hq hf hk.fresh,gem_obeys j hp hu h hq hf hk.again,?_⟩
  rw [show _-_ =(fun i=>gemL (L i) ((F-H) i)) from funext fun i=> by
    have hu := (hk.fresh.choose_spec.2 i).summable (ling_one (hv i)); have hh := (hk.again.choose_spec.2 i).summable (ling_one (hv i)); exact Eq.symm (gem_less hu hh _)]
  exact gem_obeys j hp hu h hq hf hk.moves
lemma veil_contract (h : RowBoth y δ M Q v) (hx : 0 ≤ δ) : RowBoth y δ (fun i=> veiled (M i)) (fun i=> veiled (Q i)) v := by
  constructor
  · obtain ⟨f,hf,H⟩:=h.1; exact ⟨_,hf,fun i=> veiled_price (H i) (mul_nonneg (hf.positive i) zero_le_one)⟩
  · obtain ⟨f,hf,H⟩:=h.2; exact ⟨_,hf,fun i=> veiled_price (H i) (mul_nonneg (hf.positive i) zero_le_one)⟩
  obtain ⟨f,hf,H⟩:=h.3; exact ⟨_,hf,fun i=> by change (veiled (M i)-veiled (Q i)).strip _ _; rw [← veiled_minus]; exact veiled_price (H i) (mul_nonneg (hf.positive i) (hx i))⟩
lemma scanned_contract (h : RowBoth y δ B T v) (hv : η ≤ v) (hu : Audience y) (hδ : 0 ≤ δ) : RowBoth y δ (fun i=> scan (B i)) (fun i=> scan (T i)) η := by
  constructor
  · obtain ⟨f,hf,H⟩:=h.1; refine ⟨_,hf.plus Weighed.one hu,fun i=> strip_mono (scan_fee (H i)) (hv i) ?_⟩
    simp only [Pi.one_apply,Pi.add_apply,mul_one,max_le_iff]; exact ⟨by linarith,by have hp : 0≤ f i:= hf.positive i; linarith⟩
  · obtain ⟨f,hf,H⟩:=h.2; refine ⟨_,hf.plus Weighed.one hu,fun i=> strip_mono (scan_fee (H i)) (hv i) ?_⟩
    simp only [Pi.one_apply,Pi.add_apply,mul_one,max_le_iff]; exact ⟨by linarith,by have hp : 0≤ f i:= hf.positive i; linarith⟩
  obtain ⟨f,hf,H⟩:=h.3
  exact ⟨_,hf,fun i=> scan_moves (strip_mono (H i) (hv i) le_rfl) (mul_nonneg (hf.positive i) (hδ i))⟩
end YM.RG08
end
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G : Gauge} {w : ℝ} {r e i j E : ℕ}
variable {I : Type} {P : I→Patch} {v δ η σ : I→ℝ} {y : I→ℝ}
    {A B : ∀ i, Row (Fink G (P i).L) (Fink G (P i).L)} {M Q : ∀ i,Row (Fink G (P i).L) (Loc G 1)}
    {F H : I → Air G} {ν : G.ColorIndex} {κ : KernelChoices} {D : ChartRatio G}

abbrev ticketReach (E : ℕ) := StartEnd E*(E+3)
-- defaults finite neighbor requirements; v chosen after widths
structure NutWallet (P : I→Patch) (ν : G.ColorIndex) (D : ChartRatio G) (κ : KernelChoices)
    (E : ℕ) (y v : I→ℝ) : Prop where
    pos : Audience y
    small : v ≤ 1
    crop : Weighed y (fun i=>((P i).L.val:ℝ))
    post : ∀ j≤ E,∀ k≤j+2, Weighed y (fun i=> tariffTok ν (P i) D κ j k)

private lemma max_board (ht : e≤E) (he : r≤ e+2) (hw : 0≤η)
    (h : ticketReach E • η ≤ v) : funding e (terrace e) • ((r+1:ℕ) • η) ≤ v ∧ (r+1:ℕ) • η ≤ v := by
  have hh : (funding e (terrace e) • ((r+1:ℕ) • η)) ≤ v := le_trans (by
    rw [← mul_smul]; apply smul_le_smul_of_nonneg_right _ hw; exact Nat.mul_le_mul (strict_funding ht) (by omega)) h
  constructor; exact hh
  refine le_trans ?_ hh; have hp : 1 ≤ funding e (terrace e) := Nat.succ_le_of_lt (by unfold funding; positivity)
  simpa only [one_smul] using smul_le_smul_of_nonneg_right hp (show 0≤ (r+1:ℕ) • η from nsmul_nonneg hw _)

lemma harvest_g (h : NutWallet P ν D κ E y v) (hδ : 0 ≤ δ) (hp : ∀ i,0 < v i) (ht : RowBoth y δ A B v) (hq : RowBoth y δ M Q v)
    (hV : ticketReach E • η ≤ v) (he : e ≤ E) (hw : r≤e+2) (hx : ∀ i,0<η i) (hv : 0 ≤ σ)
    (hS : ∀ i, (E+3:ℕ) • v i ≤ (P i).L.val*σ i) (f : ∀ b, Gets (F b)) (g : ∀ b,Gets (H b))
    (hr : ∀ i j, RootStep 1 e r i j → Both y δ (fun b=>F b i j) (fun b=> H b i j) σ) :
    Both y δ (fun i=> scramble ν (P i) D κ (A i) (M i) (F i) e r) (fun i=> scramble ν (P i) D κ (B i) (Q i) (H i) e r) η := by
  let L (j k) (i:I) := luggage ν (P i) D κ j k
  have heL (k n) (hp:k≤E) (hK : n≤ k+2) : Voucher y 1 (L k n) v := by
    refine ⟨_,h.post k hp n hK,fun i=> glow_less (tariff_yes ν _ _ _ k n (h.small i)) le_rfl ?_⟩
    simp only [Pi.one_apply,mul_one,le_refl]
  have hη : 0 ≤ η := fun i=> (hx i).le
  obtain ⟨H₁,H₂⟩ := max_board he hw hη hV
  let X (V : I→Air G) i:= awakening ν (P i) D κ.penalty (V i)
  let Y := fun i => luggage ν (P i) D κ e r+afterT (veiled (A i)) (X F i) none 1 e r
  let S := fun i => luggage ν (P i) D κ e r+afterT (veiled (B i)) (X H i) none 1 e r
  have hE (i j) (H : RootStep 1 e r i j) : i ≤ E ∧ j ≤ i+2 := by
    obtain ⟨⟨he',q,hq⟩,hf⟩:=H; constructor <;> omega
  have hu' k j (hR : RootStep 1 e r k j) : Both y δ (fun i=> X F i k j) (fun i=> X H i k j) v := by
    have hP := hE k j hR
    have hL := heL k j hP.1 hP.2
    have ht := gem_accrue j h.crop h.pos (fun i=> (hp i).le) h.small hv (fun i=> le_trans (smul_le_smul_of_nonneg_right (by omega) ((hp _).le)) (hS i)) (hr k j hR)
    simp only [X,nuts ν _ _ κ]; exact (Both.self hL).sub ht h.pos
  have hp₁ := fun i=> Gets_awake (P i) D κ ν (f i); have hp₂:=fun i=> Gets_awake (P i) D κ ν (g i)
  have hb := wiggle (F:=X F) (H:=X H) h.pos hδ (nsmul_nonneg hη (r+1)) hp (veil_contract ht hδ) (fun i=> ⟨(hp₁ i).1,fun e r=>(hp₁ i).2 e r|>.1⟩)
      (fun i=> ⟨(hp₂ i).1,fun e r =>(hp₂ i).2 e r|>.1⟩) (fun _=> none) H₁ hu' 1
  have hz : Both y δ Y S ((r+1:ℕ) • η) := ((Both.self (heL e r he hw)).soften H₂).add hb h.pos
  have hQ := scanned_contract hq H₂ h.pos hδ
  have hP := remit hx h.pos hδ hz hQ (show Weighed y (fun _=> (Fintype.card (Loc G 1) : ℝ)) from Weighed.constant y (by positivity))
  unfold scramble; apply (show Both y δ _ _ η from ?_); change Both y δ (-(fun i=> scrollL (Y i) (scan (M i)))) (-(fun i=> scrollL (S i) (scan (Q i)))) η; simpa using hP.weight (-1)
end YM.RG08
