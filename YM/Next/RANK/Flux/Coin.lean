import YM.Next.RANK.Flux.Striker
import YM.Next.RANK.Flux.Wraith

/-!
# Weighted budgets via tagged majorants

Keep scaled weights through ALL restricted-log uses. Need strong output K
reserve once. Here measure actual functions per entire universe of link states. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e a b y : ℝ}

lemma panel_charge (S : ι→ Plug G ζ t) (P : κ→Lining G ζ t) (v : Party S P) (U) (r : V→ℝ) (h : ∀ i,0 < r i) :
    Poly.price r ((panel S P v).tolls U) ≤ ∏ i∈v.val, Poly.price r ((speck S P i).covets U) := by
  rw [pan_price];split_ifs
  · rw [Poly.zero_price];exact prod_nonneg fun i _=> Poly.nonnegative h _
  exact Poly.multiple h _ _

set_option synthInstance.maxSize 384 in
lemma dest (S : ι→ Lifted G ζ t) (P : κ→ Lining G ζ t) (v : Party (Plug.raid ∘ S) P) (U) (r : V→ℝ) (h : ∀ i,0<r i)
    (ω : ι⊕κ→ℝ) {W : ℝ} (hp : 1 ≤ W)
    (hv : ∀ i,W*Poly.price r ((S i).amount U) ≤ ω (.inl i))
    (ht : ∀ i,Poly.price r ((raised (P i)).covets U) ≤ ω (.inr i)) :
    W* Poly.price r ((toRain S P v).amount U) ≤ panda (Plug.raid ∘ S) P ω v := by
  let X:= Plug.raid ∘ S
  have he:(panel X P v).tolls U=(toRain S P v).amount U:=congr_arg (fun p:Plug G ζ t=>p.tolls U) (congr_fun (rainbows ..) v)
  rw [← he]; let m i:= Poly.price r ((speck X P i).covets U); have hx i:0≤ m i:= Poly.nonnegative h _
  have hM i: m i≤ ω i:= by
    cases i with
    | inl i=>exact (le_mul_of_one_le_left (hx (.inl i)) hp).trans (hv i)
    | inr i=>exact ht _
  apply (mul_le_mul_of_nonneg_left (panel_charge X P v U r h) (zero_le_one.trans hp)).trans
  obtain ⟨i,hi⟩:=leaning X P v; have ht := mem_toLeft.mp hi; change W*(∏ k∈v.val,m k) ≤ ∏ k∈v.val,ω k
  rw [← Finset.mul_prod_erase _ m ht,← Finset.mul_prod_erase _ ω ht,← mul_assoc]
  apply mul_le_mul (hv _) (prod_le_prod (fun i hi=>hx i) (fun i _=>hM _)) (prod_nonneg (fun i _=>hx _)) ((hx _).trans (hM _))

variable (S : ι→ Plug G ζ t) (P : κ→Lining G ζ t)

-- classification for first Panel: $w=i in pure. Pet marklessness and pure condition separately required in restoration

def clean (s : ι→Prop) (v : Party S P):= v.val.toRight=∅∧∀ i∈v.val.toLeft,s i
def factor (p : Prop) (W : ℝ) := if p then W else 1
lemma raised_one {W : ℝ} (h : 1≤W) (p) : 1≤factor p W:= by unfold factor;split;exact h;exact le_rfl

-- Marker root argument with sign scaling. Ratio relation raw. No choose weights in forecasts once uses.
lemma Jlog (s : ι→Prop) (U : Config G n) (v : Party S P) (f : ι⊕κ → ℝ) (r : V→ℝ) {p W : ℝ}
    (hP : 1≤p) (hp : 1≤W) (H : ∀ i,0 < r i)
    (hv : ∀ i : ι, if (S i).landed then W*Poly.price r ((S i).tolls U) ≤ f (.inl i) else factor (¬ s i) p *Poly.price r ((S i).tolls U) ≤ f (.inl i))
    (h : ∀ i : κ,p*Poly.price r ((raised (P i)).covets U)≤f (.inr i)) :
    if (panel S P v).landed then W*Poly.price r ((panel S P v).tolls U) ≤ panda S P f v else
      factor (¬ clean S P s v) p * Poly.price r ((panel S P v).tolls U) ≤ panda S P f v := by
  let k(i) := Poly.price r ((speck S P i).covets U)
  have hh i:0≤k i:=Poly.nonnegative H _
  have hz i:k i≤f i:= by
    cases i with
    | inl i=>
      unfold k; rw [show speck S P (Sum.inl i)= _ from (show speck S P _= CoverReads.ofPlug (S i) from rfl),p_coverVal]; have hx:=hv i;split_ifs at hx
      · exact (le_mul_of_one_le_left (Poly.nonnegative H _) hp).trans hx
      exact (le_mul_of_one_le_left (Poly.nonnegative H _) (raised_one hP _)).trans hx
    | inr i=> exact (le_mul_of_one_le_left (hh _) hP).trans (h i)
  let u:= panel S P v
  have hq (m : ℝ) (hv : 1 ≤ m) (i : ι ⊕κ) (hi : i∈v.val) (hr : m*k i≤f i) : m* Poly.price r ((panel S P v).tolls U) ≤ panda S P f v:= by
    apply (mul_le_mul_of_nonneg_left (panel_charge S P v U r H) (zero_le_one.trans hv)).trans; change m*(∏ i∈v.val,k i) ≤ ∏ i∈v.val,f i
    rw [← mul_prod_erase _ k hi,← mul_prod_erase _ f hi,← mul_assoc]; exact mul_le_mul hr (prod_le_prod (fun i _=> hh i) (fun i _=>hz i)) (prod_nonneg fun i _=> hh i) ((hh _).trans (hz _))
  split
  · rename_i he; have hx:(vital S P v).Nonempty:= pan_vital S P v ▸ (show (panel S P v).inventory.Nonempty from he)
    obtain ⟨x,hx⟩:=hx; obtain ⟨i,hi,hc⟩:=mem_biUnion.mp hx
    have hh:= hv i; rw [if_pos (show (S i).landed from ⟨x,hc⟩)] at hh
    apply hq W hp _ (mem_toLeft.mp hi); unfold k; change W*Poly.price r ((CoverReads.ofPlug (S i)).covets U) ≤ _; rw [p_coverVal]; exact hh
  rename_i he; obtain ⟨i,hi⟩:=leaning S P v
  have hf b (hp:b∈v.val.toLeft): ¬ (S b).landed:= cool S P v (fun h=> he (show (panel S P v).inventory.Nonempty from (pan_vital S P v).symm ▸ h)) hp
  unfold factor; split
  · rename_i hu
    by_cases hk:v.val.toRight=∅
    · unfold clean at hu; push Not at hu
      obtain ⟨i,hi,hQ⟩:=hu hk
      have hh:=hv i; rw [if_neg (hf i hi),factor,if_pos hQ] at hh
      apply hq p hP _ (mem_toLeft.mp hi); unfold k;change p*Poly.price r ((CoverReads.ofPlug (S i)).covets U) ≤ _; rw [p_coverVal]; exact hh
    obtain ⟨j,hj⟩:=nonempty_iff_ne_empty.mpr hk; exact hq p hP _ (mem_toRight.mp hj) (h j)
  exact hq 1 le_rfl _ (mem_toLeft.mp hi) (by rw [one_mul]; apply hz)

section
variable [Fintype ι] [Fintype κ]
variable (H : Bright (panel S P))

omit [Fintype ι] [Fintype κ] in
lemma budget_squeeze (s : ι→Prop) (f : ι⊕κ→ℝ) (r : V→ℝ) {p W : ℝ}
    (hP : 1≤p) (hp : 1≤W) (ht : ∀ i,0 < r i)
    (hv : ∀ i U, if (S i).landed then W*Poly.price r ((S i).tolls U) ≤ f (.inl i) else factor (¬ s i) p *Poly.price r ((S i).tolls U) ≤ f (.inl i))
    (h : ∀ i U,p*Poly.price r ((raised (P i)).covets U) ≤ f (.inr i)) :
    (∀ i : Bright (panel S P),∀ U, factor (¬ clean S P s i.val) p * Poly.price r ((sunny _ i).amount t U) ≤ panda S P f i.val) ∧
      (∀ i : Dimmed (panel S P),∀ U,W * Poly.price r ((evening _ i).amount U) ≤ panda S P f i.val) := by
  constructor
  · intro i U; have hh:=Jlog S P s U i.val f r hP hp ht (fun i=>hv i U) (fun i=>h i U)
    rw [if_neg i.property] at hh; have hb (U): (panel S P i.val).tolls U=((sunny (panel S P) i).amount t U):= congr_arg (fun p:Plug G ζ t=>p.tolls U) (bright_valid _ _)
    rw [hb] at hh;exact hh
  intro i U; have hh:=Jlog S P s U i.val f r hP hp ht (fun i=>hv i U) (fun i=>h i U)
  rw [if_pos i.property] at hh
  have hb U : (panel S P i.val).tolls U= (evening (panel S P) i).amount U:= congr_arg (fun p:Plug G ζ t=>p.tolls U) (dim_valid _ _)
  rw [hb] at hh;exact hh
end

section
variable [DecidableEq ι] [Fintype ι]
lemma bond_factor (s : ι → Prop) (X : ι → SourceAt G ζ) (t : ℝ) (p : ι →ℝ) (r : V→ℝ) {y : ℝ} (ht : ∀ i,0 < r i) (he : 1 ≤ y) (q : MergeLog X) U
    (h : ∀ i,factor (¬ s i) y * Poly.price r ((X i).amount t U) ≤ p i) : factor (¬∀ i∈q.val,s i) y * Poly.price r ((Bond X q).amount t U) ≤ hlog X p q:= by
  rw [plays,Poly.adapted,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (mul_le_mul_of_nonneg_left (Poly.multiple ht _ _) (zero_le_one.trans (raised_one he _))).trans
  let v i:= Poly.price r ((X i).amount t U); have hv i:0 ≤ v i:= Poly.nonnegative ht _
  have hz i:v i ≤ p i := (le_mul_of_one_le_left (hv i) (raised_one he (¬s i))).trans (h i)
  change factor (¬ _ ) y * (∏ i ∈ q.val,v i) ≤ _; unfold factor; split
  · rename_i H; push Not at H
    obtain ⟨i,hi,hv'⟩:=H; rw [← mul_prod_erase _ v hi,← mul_prod_erase _ p hi,←mul_assoc]
    have H:=h i; rw [factor,if_pos hv'] at H; exact mul_le_mul H (prod_le_prod (fun i _=>hv i) (fun i _=>hz i)) (prod_nonneg fun i _=> hv i) ((hv _).trans (hz _))
  rw [one_mul]; exact prod_le_prod (fun i _=>hv i) (fun i _=>hz i)
end
end YM.Next.Rank.Flux
