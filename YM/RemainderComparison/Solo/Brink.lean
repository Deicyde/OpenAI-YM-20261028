import YM.RemainderComparison.Solo.Fibre
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
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){T' S' p' δ B' τ ε:ℝ}
local notation "Z" => radiusB x
local notation "C'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S C' (ConnectedActivityE6.lengths T R)

def echo (z:H.fragrances) : Syllable M H z := fun _=>Tickets.none _
local notation "echo'" => echo M H
omit [Fintype ι] in
lemma calls (z:H.fragrances) : notes M H z (echo' z)=0∧ Halo.gross M H z (echo' z)=Height.breadth H z ∧ invests M H z (echo' z) l=1:=by
   have he (t:Option (Fin z.1)): ((echo' z) t).reach=∅:=by simp [echo,Tickets.reach,Tickets.none]
   simp only [notes, Halo.gross,invests]; simp only [he, sdiff_empty]; simp only [echo,Tickets.none,card_empty,sum_const_zero,prod_empty,prod_const_one,Height.breadth,and_self]

omit [Fintype ι] in
lemma songs (z:H.fragrances): string M H χ z (echo' z)=fun V=>stream H χ V z:=by
   ext; unfold string echo stream Gas.term; simp_rw [Lyric.pivot]; unfold cadence; ring

def Scorched (z:H.fragrances) := ∃ k v,  v ∈ (z.2 k).val ∧ Halo.inherited S E v
omit [Fintype ι] in
lemma sips (z:H.fragrances): Halo.dyed M H E z (echo' z) ↔ Scorched H E z:=by
   unfold Halo.dyed Scorched; apply exists_congr; intro a; apply exists_congr; intro i
   have hz: (echo' z a).reach=∅:= by simp [Tickets.reach,echo,Tickets.none]
   rw [hz,sdiff_empty,and_comm]

lemma spark (z:H.fragrances)(hz: Solo.Scorched H E z) : 1 ≤ Height.breadth H z:= by
   obtain ⟨k,v,hp,-⟩:=hz; exact le_trans (show 1≤(z.2 k).val.card from Nat.succ_le_of_lt (card_pos.mpr ⟨_,hp⟩)) (single_le_sum (f:=fun i=>(z.2 i).val.card) (fun i _=> Nat.zero_le _) (mem_univ k))

include M
omit [Fintype ι] in
lemma wants {z:H.fragrances}(hz: Solo.Scorched H E z)(ht:Height.breadth H z<2)(hv:∃ V, stream H χ V z≠0) : ∃ i∈E,z=icon H i:=by
   obtain ⟨W,hP⟩:=hv; have hp:= (grown M H χ z (echo' z) W (show string M H χ z _ W≠0 from by rw [songs]; exact hP)).2.1
   have hh k : 1≤(z.2 k).val.card:= Nat.succ_le_of_lt (card_pos.mpr (hp k).1.1)
   obtain ⟨j,v,hv,i,he,rfl⟩:= hz
   exact ⟨_,he,Beam.lantern z hh (by omega) j hv⟩

variable (p₁:H.ThinP→Drums M S→ℝ) {w x₁:ℝ}
local notation "z'" => (Captain.reachability (H:=H))
omit M [Fintype ι] in
lemma locus (z:H.fragrances) : (Beam.dashboard H z).support=z' z:= Beam.see ..
lemma concierge (hl:∀i,0≤ l i)(hp: Paid M H χ N p₁)
    (hX: Ac.Hit z' Z (fun z=>∑ i:Syllable M H z, if (Halo.dyed M H E z i ∧ 1+k≤Halo.gross M H z i) ∧ Lyric.notes M H z i≤ m then Lyric.Bill M H p₁ z l j i J else 0) a x₁) :
    Footprint.Anchored (fun i=>(Beam.dashboard H i).site) (fun i=> if Scorched H E i ∧ 1+k≤ Height.breadth H i then dividend M H i (echo' i) p₁ j J else 0)
          (fun i=>coverNumber Z (Captain.reachability (H:=H) i)) a x₁:=by
    intro x'; refine budget_mono (hX x') (fun i=>?_) (fun i=>?_)
    · dsimp only; split_ifs; exact mul_nonneg (dividend_nonneg M H χ hp _ _) (Real.exp_pos _).le; exact mul_nonneg le_rfl (Real.exp_pos _).le; exact le_rfl
    dsimp only; split_ifs
    next h hs h'=>
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; let u:=echo' i; have hz:=calls M H l i
       rw [← show Lyric.Bill M H p₁ i l j u J= dividend M H i (echo' i) p₁ j J from ?_]; swap; · unfold Bill; rw [show Lyric.invests M H i u l =1 from hz.2.2,one_mul]
       let f v:=if (Halo.dyed M H E i v∧ 1+k ≤ Halo.gross M H i v)∧ Lyric.notes M H i v≤ m then Lyric.Bill M H p₁ i l j v J else 0
       have hf:f u=Lyric.Bill M H p₁ i l j u J:=by unfold f; exact if_pos ⟨⟨(sips M H E i).2 hs.1, hz.2.1.symm ▸ hs.2⟩,by unfold u; rw [hz.1]; exact Nat.zero_le _⟩
       refine le_trans hf.symm.le (Finset.single_le_sum (f:=f) (fun i _=>?_) (Finset.mem_univ u))
       unfold f; split
       · exact mul_nonneg (prod_nonneg fun i _=> prod_nonneg fun s _=>hl _) (dividend_nonneg M H χ hp _ _)
       exact le_rfl
    next h hs he=> exact (he (by rw [← locus, ← h]; exact (Beam.dashboard H i).anchor)).elim
    all_goals have hh:=(hX x').1 i; simp only at hh; split_ifs at hh; first| contradiction| (simp only [zero_mul]; exact hh)|exact hh
end YM.RemainderComparison.Solo
