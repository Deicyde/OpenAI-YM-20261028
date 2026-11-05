import YM.RG08.Pivot.Checks
import YM.RG08.Door.Snow

/-! # Matrix policies. Uniform UV rate, primary real per cover -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Reflect Finset Needle Source Source.Drops Labels Planned.PrimaryIntegral295
open Conductor Door
open scoped Topology BigOperators
variable {G : Gauge} {R:ℝ} {d r j l n e D E τ : ℕ} {H : Hol G} {F: Labels.Frame G d} {Ω: SectionData F}

section
variable {I : Type} {y s w a κ : I→ℝ}{U V:I →EnvelopeU D R G (r+2)}{P Q:I→Row (Loc G 1) (Loc G 1)}
lemma tin_flix {w' : I→ℝ}(h: Tin y a U w)(hw : 0≤w)(hp : Weighed y κ)(he:∀ i, Plaque (P i) (κ i*w' i)) :
    Tin y (w'*a) (fun i=> jib none (P i) (U i)) w:= by
  obtain ⟨A,hA,H⟩:=h.serves
  refine ⟨_,(Weighed.constant y (norm_nonneg (batting r))).times (hp.times hA),fun i=> Ink.raise (fil_exp (H i) (hw i) (he i)) (le_of_eq ?_)⟩
  simp only [Pi.mul_apply]; ring
lemma duo_chime {v w':I→Spine (Voice D R) (Loc G 1)}(h : ∀ r,Twill y a (fun i=> v i r) (fun i=>w' i r) w) (he:Audience y)(_ : 0≤a)(hw:0≤w)(hp:Weighed y κ)(hA:∀ i,Plaque (P i) (κ i) ∧ Plaque (Q i) (κ i) ∧ Plaque (P i-Q i) (κ i*a i))(n r):
    Twill y a (fun i=> frisk (P i) (v i) n r) (fun i=> frisk (Q i) (w' i) n r) w := by
  unfold frisk; refine Twill.sums (range (n+1)) he ?_; intro i _hi; clear _hi n
  induction i generalizing r with
  | zero=> simp_rw [fig]; exact h _
  | succ n ih=>
    simp_rw [fig]
    apply Twill.weight (F:=fun i=>jib none (P i) _) (H:=fun i=> jib none (Q i) _) _ _ he
    let U i:= fig (P i) (v i) n (r+2); let V i:=fig (Q i) (w' i) n (r+2)
    have ht : Twill y a U V w:= ih (r+2)
    have h1 :∀ i, Plaque (P i) (κ i * (1:I→ℝ) i):= by intro i; rw [Pi.one_apply,mul_one]; exact (hA i).1
    have h2 :∀ i, Plaque (Q i) (κ i * (1:I→ℝ) i):= by intro i; rw [Pi.one_apply,mul_one]; exact (hA i).2.1
    have hc:= tin_flix ht.goes hw hp h1; have hC:= tin_flix (P:=P-Q) (w':=a) ht.two hw hp (fun i=> (hA i).2.2)
    rw [one_mul] at hc; rw [mul_one] at hC
    refine ⟨by simpa only [one_mul] using tin_flix ht.one hw hp h1, by simpa only [one_mul] using tin_flix ht.two hw hp h2,?_⟩
    convert hc.plus hC he using 1
    funext i
    simp only [Pi.sub_apply,Pi.add_apply,phil_less (hA i).1 (ht.one.solo hw i) (ht.two.solo hw i),phil_bet (ht.two.solo hw i) (hA i).1 (hA i).2.1]
    unfold U V; abel
end

section
open Wings
variable {I: Type}{m:I→Windows}{X:Chain}{ν:G.ColorIndex}{Z:ChartRatio G} {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S: Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D}{T: Signals P Q E τ H Ω h hD}(he:Tights T S ν Z m){A:Quilt X.kernel.penalty g.w}(hx:Plays (X:=X) m A)
local notation "Υ" => Ye (u:=m) X ν Z T
local notation "ℌ" => oven X ν Z H Ω (d.le_succ.trans hD) h
local notation "Ⓨ" => menu X
local notation "ϕ" => chop X (1/4)
include he hx
lemma ponderous : ∃ c : Wings m 0 →ℝ, Weighed Ⓨ c ∧∀ i,
    let P:= fires X G i.N i.i; let Q:= fires X G i.M i.i; Plaque P (c i) ∧ Plaque Q (c i) ∧ Plaque (P-Q) (c i*ϕ i) := by
  obtain ⟨_,c,-,hc,H⟩:=harvest he.hc hx
  refine ⟨c,hc,fun i =>?_⟩; intro P Q
  refine ⟨⟨hc.positive i,fun a b x=>?_⟩,⟨hc.positive i,fun a b x=>?_⟩,⟨mul_nonneg (hc.positive i) (gain_pos ..).le,fun a b x=>?_⟩⟩
  · unfold P fires plaza YM.RG08.colored; split; exact (H i|>.2.2 _ _ x).1; rw [norm_zero]; exact hc.positive _
  · unfold Q fires plaza YM.RG08.colored; split; exact (H i|>.2.2 _ _ x).2.1; rw [norm_zero]; exact hc.positive _
  simp only [P,Q,plaza,YM.RG08.colored,Pi.sub_apply]; split; exact (H i|>.2.2 _ _ x).2.2; rw [sub_zero,norm_zero]; exact mul_nonneg (hc.positive i) (gain_pos ..).le
lemma harvested (b:Letter F)(r): Twill Ⓨ ϕ
    (fun i:Wings m 0=> frisk (fires X G i.N i.i) (Υ i b 0) d r)
    (fun i:Wings m 0=> frisk (fires X G i.M i.i) (Υ i.wingR b 0) d r) (fun i=> ώ T i.i) := by
  obtain ⟨c,hc,H⟩:=ponderous he hx
  exact duo_chime (fun i=> yellow he (Nat.zero_le E) b i) (sh X) (fun i=> (gain_pos ..).le) (fun i=>(T.pos _).le) hc H d r
lemma bells : Lying Ⓨ ϕ (fun i:Wings m 0=>ℌ i.N i.i) (fun i:Wings m 0=> ℌ i.M i.i) := by
  obtain ⟨c,hc,H'⟩:=ponderous he hx
  intro a b
  let f i:= frisk (fires X G (N i) ((i:Wings m 0).i)) (Υ i b 0) d (slot a); let q (i:Wings m 0):= f i.wingR
  have hv : Twill Ⓨ ϕ f q (fun i=>ώ T i.i):= harvested he hx b (slot a)
  have hp (i:Wings m 0): 0<ώ T i.i:= T.pos _
  have hπ (i:Wings m 0): ώ T i.i ≤ 1:= (tick_t T _|>.1).trans ((tick_t T _|>.2).trans (min_le_right ..))
  have hΔ : Weighed Ⓨ (fun i:Wings m 0=> (ώ T i.i)⁻¹):= he.he.costs.transfer toLaunch
  have ht i: Gold (f i):= gold_sum (fun j _=> golden_terraces X.kernel.penalty_pos (X.adm i.i) (W:= Υ i b 0) (fun j=> sober_vetted ((he.firs i).rank b)) _ (slot a) j)
  have hg i: Polished (f i):= polished_sum (fun j _=> pol_front (U:= Υ i b 0) (H' i|>.1) ((he.firs i).paid b 0) j (slot a))
  refine ⟨(digs H hv.one hp hπ hΔ a).rates,(digs H hv.two hp hπ hΔ a).rates,?_⟩
  obtain ⟨B,hB,F⟩:= (digs H hv.goes hp hπ hΔ a).asset
  refine ⟨B,hB,fun i=>?_⟩
  change ‖invest H (f i) a-invest H (f i.wingR) a‖ ≤ _; rw [← Pivot.invest_less H a (hg _) (hg _) (ht i).toToute (ht _).toToute]; exact F i
lemma bellsR : Lying Ⓨ ϕ (fun i:Wings m 0=> (ℌ i.N i.i)⁻¹) (fun i:Wings m 0=> (ℌ i.M i.i)⁻¹) := by
  have hh:= bells he hx; let P i:=1-ℌ (N i) ((i:Wings m 0).i); let Q (i:Wings m 0):= P i.wingR; have ht : Lying Ⓨ ϕ P Q := by
    unfold P Q; simp_rw [sub_eq_add_neg]; exact ((Lying.fixed (δ:=ϕ) (hp:=sh X) (U:= (1: Loft F))).plus (sh X) (Lying.neg (sh _) hh))
  have heq (i:Wings m 0): (ℌ i.N i.i)⁻¹=shellP (P i) := by
    obtain ⟨_,_,H⟩:= portion G X.kernel.penalty_pos (X.adm i.i); exact (settled_hearth _ (he.firs i) (H _|>.1)).2
  intro i j; change Lease _ _ _ (fun u : Wings m 0=> (ℌ u.wingR.N u.wingR.i)⁻¹ i j); simp_rw [heq]; exact Lying.many (sh X) _ (fun k (_: k∈ range _)=> Lying.powers (sh X) ht k) i j
-- give on any column chart map already paid by RG06
lemma picks_pre (J : Loft F) : Lying Ⓨ ϕ (fun i:Wings m 0=>(ℌ i.N i.i)⁻¹*J) (fun i:Wings m 0=>(ℌ i.M i.i)⁻¹ * J) :=
    Lying.times (sh X) (bellsR he hx) (Lying.fixed (sh X) J)
end
end YM.RG08.Pivot
