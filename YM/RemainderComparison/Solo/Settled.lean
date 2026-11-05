import YM.RemainderComparison.Solo.Brink

/-!
 # All genuine-`E` clauses on actual α. Stronger neighboring exponents

 Don't charge anything after reclosure here. To Step4 exacter: preserve
 the scalar/affine extraction costs. This is the before-Book Boot,
 also valid at the threshold seam. Deploy on Frame pilot of this post setup.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Halo Graft Cascade Lyric Daisy
open Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N:Captain H j q d v u A b r B e n χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){b' T' S' p' δ B' τ ε η:ℝ}
local notation "Z" => radiusB x
local notation "z'" => (Captain.reachability (H:=H))
variable (p₁:H.ThinP→Drums M S→ℝ)
local notation "ow" => (fun z=> dividend M H z (echo M H z) p₁ j J)

structure Supply (H:Cash W x μ L Q o C T R)(χ:Chi)(E:Set ℕ)(B: BudgetPoint)(ε σ : ℝ):Prop where
   grants : ∃ w:H.fragrances→ℝ,(∀ i,∀ _ : Solo.Scorched H E i, let p:=Beam.dashboard H i
       let f V:= stream H χ V i; B.Regular p.support f ∧ B.supBounds p.site p.support f (w i)) ∧
      (∀ i,0 ≤ w i) ∧ Footprint.Anchored (fun i=>(Beam.dashboard H i).site) w (fun i=>coverNumber B.B (reachability (H:=H) i)) ε σ
lemma solo (P':BudgetPoint)(ht:P'.threshold=Pressure.temp x)(hh:P'.B=Z)(hn:P'.order≤j)(hN:P'.power≤J)(_h:Presents R E w δ)
     (hZ:Brim.Scores P' H χ E S' ε)(hp:Lyric.Paid M H χ N p₁)(hl:∀ i,0≤ l i)
     (ha:a=ε+η)(hi:0≤η)
     (hx:∀ k:ℕ,Ac.Hit z' Z (fun z=>∑ i:Syllable M H z, if (Halo.dyed M H E z i ∧ 1+k≤ Halo.gross M H z i)∧Lyric.notes M H z i ≤ m then Lyric.Bill M H p₁ z l j i J else 0) a (κ*b'^k*δ)) : -- param
      Supply H χ E P' ε (S'+(κ*b'+Real.exp (-η*Z)*κ)*δ) :=by
   obtain ⟨s,hG,hY,hm,hT⟩:= hZ.grants
   let t :=Function.extend (Brim.icon H) s 0
   have hz z : 0≤ t z :=by
      by_cases he:z∈ Set.range (Brim.icon H)
      · obtain ⟨i,rfl⟩:=he; rw [show t (icon H i)=s i from (Beam.icon_inj H).extend_apply s 0 i]; exact hm i
      rw [show t z= (0:H.fragrances→ℝ) z from Function.extend_apply' _ _ _ he]; rfl
   have hh' (z): (Beam.dashboard H z).support=z' z:=locus H z
   let d (z:H.fragrances):= coverNumber P'.B (z' z)
   have he: Footprint.Anchored (fun i=>(Beam.dashboard H i).site) t d ε S':=by
      intro x; let e':ℕ↪ H.fragrances:= ⟨Brim.icon H,Beam.icon_inj _⟩; apply Beam.wallet e'
      · convert hT x using 1; ext i; change (if (Beam.dashboard H (icon H i)).site=x then t (icon H i)*_ else 0)=_
        unfold d; rw [show t (icon H i)=s i from e'.injective.extend_apply s 0 i, ← hh', Beam.impact, show (Beam.dashboard H (e' i))=_ from Beam.impact H i]
      intro z hp; split; next h=> rw [show t z=0 from Function.extend_apply' _ _ _ hp,zero_mul]
      next=>rfl
   let tall z:= Solo.Scorched H E z∧ 2≤ Height.breadth H z
   let far z:= Solo.Scorched H E z∧ Z < d z
   have hP z: P'.Regular (z' z) (fun V=>stream H χ V z) ∧ P'.supBounds (Beam.dashboard H z).site (z' z) (fun V=>stream H χ V z) (ow z):=by
      rw [← Solo.songs M]
      obtain ⟨hP,hH⟩:=direction M H χ hp z (Solo.echo M H z) P' ht hn J hN
      exact ⟨hP,hH _ (by rw [← hh']; exact (Beam.dashboard H z).anchor)⟩
   let f z:= if tall z then ow z else 0; let g z:= if far z then ow z else 0
   have hf z:0≤f z:=by unfold f; split; exact (hP z).2.1; exact le_rfl
   have hg z:0≤g z:=by unfold g; split; exact (hP z).2.1; exact le_rfl
   refine ⟨fun i=> t i+(f i+g i),fun i hp=>?_,fun i=>add_nonneg (hz i) (add_nonneg (hf i) (hg i)),?_⟩
   · dsimp only; rw [hh' i]; have ht : ∀ {q} (h:P'.supBounds (Beam.dashboard H i).site (z' i) (fun V=>stream H χ V i) q), q≤t i+(f i+g i) →  (P'.Regular (z' i) (fun V=> stream H χ V i) ∧ P'.supBounds (Beam.dashboard H i).site (z' i) (fun V=>stream H χ V i) (t i+(f i+g i))) := fun h hh=>⟨(hP i).1,(show P'.supBounds _ _ _ (t i+(f i+g i)) from ⟨add_nonneg (hz i) (add_nonneg (hf i) (hg i)),fun _ he z hP hQ=> (h.2 _ he z hP hQ).trans hh⟩)⟩
     by_cases hh:tall i; · exact ht (hP i).2 (le_trans ((show ow i=f i from (if_pos hh).symm).trans_le (le_add_of_nonneg_right (hg i))) (le_add_of_nonneg_left (hz i)))
     by_cases hr:far i; · exact ht (hP i).2 (le_trans ((show ow i=g i from (if_pos hr).symm).trans_le (le_add_of_nonneg_left (hf i))) (le_add_of_nonneg_left (hz i)))
     have hy:Height.breadth H i < 2:= lt_of_not_ge (fun h'=> hh ⟨hp,h'⟩)
     by_cases he:∃ V:Config G c, stream H χ V i≠0
     · obtain ⟨k,hk,rfl⟩:= wants M H χ E hp hy he; apply ht (q:=s k)
       · rw [← locus,Beam.impact]; exact (hG k hk).2 (by
           have hv:d (icon H k) ≤ Z:= le_of_not_gt (fun he'=>hr ⟨hp,he'⟩); unfold d at hv; rw [← locus,Beam.impact] at hv; rwa [← ‹P'.B=Z›] at hv) -- hb affects cast
       rw [show t (icon H k)=s k from (Beam.icon_inj H).extend_apply s 0 k]; exact le_add_of_nonneg_right (add_nonneg (hf _) (hg _))
     push Not at he; apply ht (q:=0)
     · simp_rw [he]; simpa only [abs_zero] using! AnalyticBridge.CouplingShape.sup_const (G:=G) (p:=P') (o:=(Beam.dashboard H i).site) (X:=z' i) 0
     exact add_nonneg (hz i) (add_nonneg (hf i) (hg i))
   have hx k := concierge M H χ N l E p₁ hl hp (hx k)
   intro q
   have hr : SumBudget (fun i=> if (Beam.dashboard H i).site=q then f i*Real.exp (ε*d i) else 0) ((κ*b')*δ):=by
      refine budget_loosen (budget_mono (hx 1 q) (fun i=>by split; exact mul_nonneg (hf i) (Real.exp_pos _).le; exact le_rfl) (fun i=>?_)) (by rw [pow_one])
      split
      next hh=>
       apply mul_le_mul_of_nonneg_left _ (hf _)
       apply Real.exp_monotone; unfold d; rw [‹P'.B=Z›]; exact mul_le_mul_of_nonneg_right (ha ▸ le_add_of_nonneg_right hi) (Nat.cast_nonneg _)
      next=> exact le_rfl
   let A:=Real.exp (-η*Z)
   have hX: SumBudget (fun i=>if (Beam.dashboard H i).site=q then g i*Real.exp (ε*d i) else 0) (A*κ*δ):=by
      refine budget_loosen (budget_mono (budget_scale (show 0≤A from (Real.exp_pos _).le) (hx 0 q)) (fun i=>by split; exact mul_nonneg (hg _) (Real.exp_pos _).le; exact le_rfl) fun z=> ?_) (by rw [pow_zero,mul_one,mul_assoc])
      split
      next hQ=>
       by_cases hf:far z
       · dsimp only
         rw [if_pos (show Solo.Scorched H E z ∧ _ from ⟨hf.1,spark H E z hf.1⟩), show g z=ow z from if_pos hf]
         unfold A; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hP _).2.1
         apply Real.exp_monotone; unfold d; rw [hh]
         have hx: (Z:ℝ)≤ (coverNumber Z (z' z):ℝ) :=by exact_mod_cast (show Z ≤ coverNumber Z (z' z) from by have hv : Z ≤ d z:=hf.2.le; unfold d at hv; rwa [hh] at hv) 
         rw [ha]; nlinarith only [hx,hi]
       rw [show g z=0 from if_neg hf,zero_mul]; exact mul_nonneg (Real.exp_pos _).le (by have he:=(hx 0 q).1 z; dsimp only at he; rw [if_pos hQ] at he; exact he) -- edit
      next=> rw [mul_zero]
   convert budget_plus (he q) (budget_plus hr hX) using 1; swap; · unfold A; ring
   ext i; dsimp only; split
   next hi=> simp only [d,add_mul]
   next=>simp
end YM.RemainderComparison.Solo
