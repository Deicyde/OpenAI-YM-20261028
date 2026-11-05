import YM.RemainderComparison.Sleet.Post
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sleet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "D" => grow G L x
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x
lemma stepProd {α:Type*} (f:α→ℝ)(h:∀ i,1 ≤ f i){i:α}{s:Finset α}(hx:i∈s) : f i ≤ ∏ j∈s,f j:=by
   rw [← Finset.mul_prod_erase s f hx]; exact le_mul_of_one_le_right (zero_le_one.trans (h i)) (Finset.one_le_prod fun j _=>h j)

abbrev chain (S:StepData c f) (i:ChainIndex f) : Head S:= .inr (.inr (.inl (.inr (.inr i))))
abbrev flame (S:StepData c f) (i:WarningAt c f):Head S:= .inr (.inr (.inr i))
def screened (S:StepData c f) (p:Head S) := (∃ i,p=chain S i) ∨ ∃ i,p=flame S i
def tumble (z:H.fragrances):= ∃ a i, screened S i ∧ i∈(z.2 a).val
lemma slips (p:Head S) (hp:screened S p) (q:Wing) : p ≠ Wing.badge q S := by
   rcases hp with ⟨i,rfl⟩|⟨i,rfl⟩ <;> cases q <;> simp only [flame,chain,Wing.badge] <;> intro h <;> cases h
variable {P':Type} [Fintype P'] {s':P'→ Site f} {t:ι→ Finset P'}
variable (hv:Scale s' t M l m σ Gp S)(hr:radiusCost Q L σ)(h:Premium Q L x a μ b' B j n k s J m Gp)
local notation "X'" => Palette.mark M (c:=c)
local notation "λ₀" => Lyric.mulScale ((tax G L x)⁻¹) l
local notation "XX" => Lyric.ink Q L x m Gp
include hv hr h
lemma tempest (hp: Massive (region k s) N.conduit)(hq:Heroes H N.conduit A B n) :
  Ac.Hit (Captain.reachability (H:=H)) Z (fun z:H.fragrances=>∑ w:Syllable M H z, if tumble H z ∧ notes M H z w≤ k then
        Lyric.Bill M H (floats M H χ N) z l j w J else 0) a ((gStep R.beta)^s):=by
   have ht:=opening M H χ N l (region k s) hp hv hr h
   let f:= inkF S (region k s) D
   have hh i: 1 ≤ f i:=one_le_pow₀ h.roll
   have hh' p i:1 ≤ merit M H f p i:= one_le_prod fun i _=>hh i
   have hD:0<D:= zero_lt_one.trans_le h.roll
   have hp' := rocketing M H χ N hq
   have hT:1 ≤ tax G L x:=one_le_pow₀ h.roll
   have hw: ∀ z (i:Syllable M H z), tumble H z → 1 ≤ (D^(region k s))⁻¹ * ∏ a,merit M H f (z.2 a) (i a) := by
      rintro z i ⟨a,p,hp,h₁⟩
      have he : p∉ (show Drums M S from i a).reach:=by
         rw [← Palette.label]; intro H'; obtain ⟨m,hM,hV⟩:=mem_image.mp H'; exact slips p hp m.turn hV.symm
      have hz : D^region k s ≤ f p:= pow_le_pow_right₀ h.roll (by rcases hp with ⟨v,rfl⟩|⟨v,rfl⟩ <;> simp [glow,Clutch.truce,chain,flame]) -- edit use h.roll not shadow
      have hpz := hz.trans (show f p≤ merit M H f (z.2 a) (i a) from stepProd _ hh (mem_sdiff.mpr ⟨h₁,he⟩))|>.trans (stepProd (fun a=>merit M H f (z.2 a) (i a)) (fun a=>hh' _ _) (mem_univ a))
      calc _ = (D^region k s)⁻¹*D^region k s := (inv_mul_cancel₀ (by positivity)).symm
           _ ≤ _:= mul_le_mul_of_nonneg_left hpz (by positivity)
   have he:= Lyric.run M H χ (floats M H χ N) λ₀ (merit M H f) hp' (fun i=>mul_nonneg (show 0≤(tax G L x)⁻¹ by positivity) (hv.currency i)) (fun p i=> zero_le_one.trans (hh' p i)) h.visit.posts J ht (fun z _=>tumble H z) _ (by positivity) hw
   have hL:= H.laws.data.funds.length_eq; have hz : 1< betaF G x L:= hL ▸ H.laws.intake.height
   obtain ⟨hc,ht⟩:= H.laws.intake.window; rw [hL] at hc ht
   intro i; exact budget_loosen (Halo.remits M H χ N l (τ:=tax G L x) (floats M H χ N) (fun z _=>tumble H z) he hv.currency hT hp' k i) (h.bounty R.beta ⟨by linarith only [hc,hz],by linarith only [ht,hz]⟩)
omit hv hr h

def depthPrice (x:ℝ)(L:Side):ℝ:= till x/L.val
lemma narrowK (Q:ConnectedActivityE6.Target G P)(L:Side)(k:ℕ): ∀ᶠ x in atTop, grow G L x^k ≤ Real.exp (Q.ε * depthPrice x L):=by
   let p:= (L.val:ℝ)
   have hh : 0<p:= Nat.cast_pos.mpr L.property
   have ht:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow k; have he:= Rate.cutoff (G:=G) (L:=L) (div_pos Q.usable hh) (a:=-1-3/8*k)
   filter_upwards [(ht.mul he).below (by linarith only) 1 zero_lt_one] with x hx
   apply (div_le_one (Real.exp_pos _)).1; unfold depthPrice; change grow G L x^k/Real.exp (Q.ε*((till x:ℝ) /p)) ≤ 1 -- shift parens
   rw [div_eq_mul_inv, ← Real.exp_neg]; apply (le_abs_self _).trans
   rw [show -(Q.ε*((till x:ℝ)/p))= -(Q.ε/p)*(till x) by ring]; exact hx

def Flurry (z:H.fragrances)(k s:ℕ):= Beacon.large H (region k s) (depthPrice x L) z
include hv hr h
lemma snow (hQ:D^region k s ≤ Real.exp (Q.ε * depthPrice x L))
    (h': Heroes H N.conduit A B n)(hp:Massive (region k s) N.conduit) : Ac.Hit (Captain.reachability (H:=H)) Z
      (fun z:H.fragrances=>∑ w':Syllable M H z, if Flurry H z k s ∧ notes M H z w'≤k then Lyric.Bill M H (floats M H χ N) z l j w' J else 0) a ((gStep R.beta)^s):=by
   have hh:= H.laws.data.funds.length_eq
   have hX:1 < betaF G x L := hh ▸ H.laws.intake.height
   have hb:inBand (betaF G x L) R.beta:= by
      obtain ⟨ha,hb⟩:=H.laws.intake.window; rw [hh] at ha hb; exact ⟨by linarith only [ha,hX],by linarith only [hb,hX]⟩
   have hF : R.p.B ≤ 2*Z:= by rw [H.laws.intake.sizes,hh]; exact h.visit.covers
   obtain ⟨-,hh,-⟩:= Lyric.habitats M H l hv h.roll hF hr
   intro i; exact budget_loosen (Lyric.earns (Gp:=XX) M H χ l N hv.currency h.roll hh h.pace h.visit.win h.visit.allow h.stamp (narrow H χ N.conduit hp h.roll) h' h.visit.posts J (region k s) k (depthPrice x L) hQ h.retain.1 i) (h.bounty R.beta hb)
end YM.RemainderComparison.Sleet
