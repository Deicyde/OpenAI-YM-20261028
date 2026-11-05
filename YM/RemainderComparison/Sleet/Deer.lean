import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Roused
import YM.RemainderComparison.Sleet.Spark
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

lemma within (x:ℝ)(L:Side): depthPrice x L ≤ till x := div_le_self (Nat.cast_nonneg _) (by exact_mod_cast L.property)

-- invoke existing syntactic attribution on low words
variable (z:H.fragrances) (w:Syllable M H z) {V:Config G c}
variable {i:Head S}{y:Option (Fin z.1)}
lemma reserve_len (hz:i∈ (z.2 y).val)(hx : ¬ Flurry H z k s) :
    Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i < depthPrice x L := by
    let p i:=Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i
    have hp i:0≤ p i:=by
      rcases i with i | i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
    let S₀ y:=H.shapeW (z.2 y).val
    have ht : p i≤ H.shapeW (z.2 y).val:=
       (le_add_of_nonneg_left (show 0≤(coverNumber Z (H.supportP i):ℝ) from Nat.cast_nonneg _)) |>.trans (Finset.single_le_sum (f:=fun i=> (coverNumber Z (H.supportP i):ℝ)+ p i) (fun i _=> add_nonneg (Nat.cast_nonneg _) (hp i)) hz)
    exact lt_of_le_of_lt (ht.trans (Finset.single_le_sum (f:=S₀) (fun i _=> H.positive_volume _) (mem_univ y))) (lt_of_not_ge fun he=> hx (Or.inr (Or.inr he)))

abbrev pair₀ (S:StepData c f)(i:Pairs f⊕ Pairs c) : Head S:=Sum.inr (.inr (.inl (Sum.inl (Sum.inr (.inr (.inr (.inr i)))))))
def double (S:StepData c f)(i:Head S):= ∃ z,i=pair₀ S z
lemma shortPair {T:PathData G} {i:Pairs f} {d:ℕ} (hd:d≤L.val)(h:(bothCharge T i:ℝ)<depthPrice x L) : ¬ long T (till x) d i.2.1 i.2.2.2:=by
   refine not_not.mpr ?_
   let v:= T.row i.2.1; let n:=i.2.2.2; let a:= v n.1|>.2.length; let b:=v n.2|>.2.length
   have hh: ((a+b:ℕ):ℝ)*(L.val:ℝ)<till x:= (lt_div_iff₀ (Nat.cast_pos.mpr L.property)).1 (by unfold bothCharge at h; rw [Paths.duplex_price] at h; exact h)
   have h':(a+b)*L.val≤till x:=by exact_mod_cast hh.le
   exact ⟨(Nat.mul_le_mul (show a≤a+b by omega) hd).trans h',(Nat.mul_le_mul (show b≤a+b by omega) hd).trans h'⟩

lemma unpair (h: i∈(z.2 y).val)(hx : ¬ Flurry H z k s)(ht:double S i)(A : Coat T F)(hv:A.x=x)(U:Directions G f)(V:Config G f)(Z': Air f G)(w:Finset ℕ) :
    Polar.ember A o.a R W Q.table U V Z' w Q.halo i=0:=by
   have he:=reserve_len H z h hx
   obtain ⟨v,rfl⟩:=ht
   change Real.exp (Polar.frost A o.a R U V (Sum.inr (.inr (.inr (.inr v))))) -1=0
   rcases v with i|i
   · have hh:= shortPair (show 1≤L.val from L.property) (show (bothCharge R.path i:ℝ) < _ from he)
     unfold frost nest; simp only [hv,Sum.elim_inr,Sum.elim_inl,pairValue,pairTail,hh,false_and,↓reduceIte]; simp
   have hh:= shortPair (show S.patch.L.val ≤ L.val by rw [H.laws.data.funds.length_eq]) (show (bothCharge T.down i:ℝ) < _ from he)
   unfold frost nest; simp only [hv,Sum.elim_inr, icicle, Polar.twin, hh,↓reduceIte]; simp

open Greenbelt Art Silica
omit [Fintype ι] in
lemma interim (he:string M H χ z w V≠0)(h:i∈(z.2 y).val)(hx: ¬Flurry H z k s) : ¬ double S i:=by
    intro ht; apply he
    let p:=(z.2 y); let u:=team M (w y)
    have hf : i∉ u.signs S:=by
        intro h; obtain ⟨a,ha,hy⟩:= mem_image.mp h
        obtain ⟨i,rfl⟩:=ht; cases he:a.turn <;> rw [he] at hy <;> cases hy
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_univ y) ?_)
    unfold toe Cascade.escort likely; rw [sum_eq_zero ?_,mul_zero]; intro r (_:r∈univ)
    unfold Team.picture; refine integral_eq_zero_of_ae ?_
    filter_upwards with q
    unfold Team.grove; split
    next hg=>
      unfold likely; rw [sum_eq_zero ?_,mul_zero]; · rfl
      intro s hs
      unfold Team.cinema; refine integral_eq_zero_of_ae ?_; filter_upwards with u
      refine integral_eq_zero_of_ae ?_; filter_upwards with v
      unfold Team.floret; apply mul_eq_zero_of_right; split
      next hh=> exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_sdiff.mpr ⟨h,hf⟩) (unpair H z h hx ht _ rfl _ _ _ _))
      next hh=> rfl
    next hh=> rfl

open Deck
omit [Fintype ι] in
lemma mood (i:Head S)(hi:i∈(z.2 y).val)(he:string M H χ z w V≠0)(hx: ¬ Flurry H z k s)(hz:¬ tumble H z): (∃ j:Mint.Music c f, Mint.disc S j=i∧ Mint.verse R.path j ≤ Z) ∨ ∃ j:ℕ, Opacity.key S j=i:=by
    have hp:= Lyric.listens M H χ z w V he (show ¬ Storm H k s z from fun ht=>hx (Or.imp_right (Or.imp_right fun h=> (within x L).trans h) ht))
    have hh:= interim M H χ z w he hi hx; have hf : ¬ screened S i :=fun s=>hz ⟨y,i,s,hi⟩
    have hG:= (reserve_len H z hi hx).le.trans ((within ..).trans (show (till x:ℝ) ≤ Z by exact_mod_cast Nat.div_le_self (radiusB x) _))
    have hL j (hp : Mint.disc S j=i): Mint.verse R.path j ≤ Z:= by
       rw [← hp] at hG; rw [Mint.balance T R]; exact_mod_cast (show (exCharge T R (Mint.note j):ℝ)≤ _ from hG)
    have hw:= hp.4 y
    rcases i with i|i|i|i
    · have he:=mem_toLeft.mpr hi; rw [hw.2.2.1] at he; simp at he
    · have he: i∈ own (z.2 y).val:=mem_toLeft.mpr (mem_toRight.mpr hi); rw [hw.2.2.2] at he; simp at he
    swap; · exact (hf (Or.inr ⟨i,rfl⟩)).elim
    rcases i with i|i|i
    · rcases i with i|i|i|i|i
      · exact Or.inr ⟨i,rfl⟩
      · exact Or.inl ⟨.inl i,rfl,hL _ rfl⟩
      · exact Or.inl ⟨.inr (.inl i),rfl,hL _ rfl⟩
      · exact Or.inl ⟨.inr (.inr (.inl i)),rfl,hL _ rfl⟩
      exact (hh ⟨i,rfl⟩).elim
    · exact Or.inl ⟨.inr (.inr (.inr i)),rfl,hL _ rfl⟩
    exact (hf (Or.inl ⟨i,rfl⟩)).elim
end YM.RemainderComparison.Sleet
