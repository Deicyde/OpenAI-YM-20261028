import YM.RemainderComparison.Sleet.Density
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



abbrev Staff := Σ z:H.fragrances,Syllable M H z
abbrev Base (z:Staff M H):= reachability (H:=H) z.1

def charge (z:Staff M H)(V:Config G c) := invests M H z.1 z.2 l * Lyric.string M H χ z.1 z.2 V
abbrev kept (k:ℕ)(z:Staff M H):=Lyric.notes M H z.1 z.2≤k

-- Hit:X.V geometry per M.Marker (run separately at finite derivative setups). ROOT independent; stronger for all origins at every site.
structure Rendition (l : ι→ℝ) (P:BudgetPoint) (U: Set (Staff M H)) (α δ:ℝ):Prop where
   receipt : ∃ w:Staff M H→ℝ,(∀ i,0 ≤ w i) ∧ (∀ i∉U,w i=0) ∧
      (∀ i∈U,P.Regular (Base M H i) (charge M H χ l i)∧∀ x∈ Base M H i,P.supBounds x (Base M H i) (charge M H χ l i) (w i)) ∧ Ac.Hit (Base M H) P.B w α δ

lemma budget_sigma {Y:Type*}{Zs:Y→Type*} [∀ i,Fintype (Zs i)] {f: Sigma Zs→ℝ}
    (h:SumBudget (fun i:Y=>∑ z:Zs i,f ⟨i,z⟩) b)(hh:∀ i,0≤f i): SumBudget f b := by
   apply budget_of_sum hh; intro s
   let X:= s.image Sigma.fst
   refine (Finset.sum_le_sum_of_subset_of_nonneg (show s ⊆ X.sigma (fun i=> (univ:Finset (Zs i))) from fun i hi=> mem_sigma.mpr ⟨mem_image_of_mem _ hi,mem_univ _⟩) (fun z _ _=>hh z)).trans ?_
   rw [Finset.sum_sigma]; exact budget_sum h X

variable (V:BudgetPoint)(hx:V.B=radiusB x)(ht: V.threshold=Pressure.temp x)(hn:V.order ≤ j)(hi: V.power ≤ J)
variable (F':H.ThinP→Drums M S→ℝ)(h':Lyric.Paid M H χ N F') (hl:∀ i,0≤l i)
include ht h' hl hn hx hi
lemma reunion (U:Set (Staff M H))(p: (z:H.fragrances)→ Syllable M H z→ Prop) {z:ℝ}[∀ i j,Decidable (p i j)]
   (hp:∀ i, i∈U → p i.1 i.2)(hs:Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z, if p z i then Lyric.Bill M H F' z l j i J else 0) a z):
     Rendition M H χ l V U a z:= by
   let c (i:Staff M H):=Lyric.Bill M H F' i.1 l j i.2 J
   let b (i:Staff M H):= if i∈U then c i else 0
   have he i:0 ≤ c i:=mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun i _=>hl i) (dividend_nonneg M H χ h' i.1 i.2)
   have hh i:0 ≤ b i:=by unfold b; split; exact he i; exact le_rfl
   refine ⟨b,hh,fun i hi=> if_neg hi,fun i hv=> ?_, fun z=>?_⟩
   · obtain ⟨i,w⟩:=i; obtain ⟨hf,hF⟩:= direction M H χ h' i w V ht hn J hi; let f:=string M H χ i w; let g':= invests M H i w l; let y:=g' • (ContinuousLinearMap.id ℝ ℝ)
     have ha: charge M H χ l ⟨i,w⟩=y ∘ f:=rfl
     rw [ha,show b ⟨i,w⟩=c ⟨i,w⟩ from if_pos hv]; have hp:0 ≤ g':= prod_nonneg fun _ _=> prod_nonneg fun _ _=>hl _
     refine ⟨AnalyticBridge.VerifiedReset.regular_mapped y hf, fun x hx'=> ⟨he _,fun U hu l hl hz=>?_⟩⟩
     rw [Push.Local.left_linear y l (f:=f) (hf.smooth _ hu) hl]; change ‖g' * _‖≤ _; rw [norm_mul,Real.norm_of_nonneg hp]; exact mul_le_mul_of_nonneg_left ((hF x hx').2 _ hu l hl hz) hp
   apply budget_sigma
   · refine budget_mono (hs z) ?_ ?_
     · intro i; apply sum_nonneg; intro j _; split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl
     intro i; by_cases h:z∈ reachability (H:=H) i
     · dsimp only; rw [if_pos h, Finset.sum_mul]; apply sum_le_sum; intro j _
       rw [if_pos (show z∈ Base M H ⟨i,j⟩ from h),hx]; by_cases hv: Sigma.mk (β:=Syllable M H) i j∈U
       · rw [show b ⟨i,j⟩=c ⟨i,j⟩ from if_pos hv,if_pos (show p i j from hp ⟨i,j⟩ hv)]
       rw [show b ⟨i,j⟩=0 from if_neg hv,zero_mul]; split; exact mul_nonneg (he ⟨i,j⟩) (Real.exp_pos _).le; rw [zero_mul]
     dsimp only; rw [if_neg h, sum_eq_zero fun j _=> if_neg (show ¬ z∈ Base M H ⟨i,j⟩ from h)]
   intro i; split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl
omit ht h' hl hn hx hi

omit [Fintype ι] in
lemma Rendition.plus {U U':Set (Staff M H)} (h:Rendition M H χ l V U a B)(h': Rendition M H χ l V U' a B') : Rendition M H χ l V (U∪U') a (B+B'):=by
   obtain ⟨u,hp,h,hQ,ht⟩:=h.receipt; obtain ⟨v,hp',hh,hQ',ht'⟩:=h'.receipt
   have he i:0 ≤ u i+v i:= add_nonneg (hp _) (hp' _)
   refine ⟨fun i=>u i+v i,he,fun i hi=> by dsimp only; rw [h _ (mt (Set.mem_union_left _) hi),hh _ (mt (Set.mem_union_right _) hi),add_zero],?_,?_⟩ -- left args maybe
   · intro i hi
     have hv {w:ℝ}(hq: w ≤ u i+v i) (h: V.Regular (Base M H i) (charge M H χ l i)∧∀ x∈ Base M H i,V.supBounds x (Base M H i) (charge M H χ l i) w) := (show V.Regular _ _∧∀ x∈Base M H i,V.supBounds x (Base M H i) (charge M H χ l i) (u i+v i) from ⟨h.1,fun x hx=> ⟨he _,fun U hU l hl hh=> ((h.2 x hx).2 U hU l hl hh).trans hq⟩⟩)
     rcases hi with hi|hi
     · exact hv (le_add_of_nonneg_right (hp' _)) (hQ i hi)
     exact hv (le_add_of_nonneg_left (hp _)) (hQ' i hi)
   intro i; convert! budget_plus (ht i) (ht' i) using 1; ext j; split <;> ring
omit [Fintype ι] in
lemma Rendition.weaken {U U':Set (Staff M H)} (h:Rendition M H χ l V U a B)(h':B ≤ B')(he:U'⊆U) (ht : v≤ a) : Rendition M H χ l V U' v B':=by
   obtain ⟨u,hp,-,hQ,h⟩:=h.receipt
   let u' (i:Staff M H):= if i∈U' then u i else 0
   have hh i:0≤u' i:=by unfold u'; split; exact hp i; exact le_rfl
   refine ⟨u',hh,fun i hi=> if_neg hi,fun i hi=> ?_,?_⟩
   · rw [show u' i=u i from if_pos hi]; exact hQ i (he hi)
   intro i; refine budget_loosen (budget_mono (h i) (fun j=>?_) (fun j=>?_)) h'
   · split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl
   split; next=>
     by_cases hz:j∈U'; swap; · rw [show u' j=0 from if_neg hz,zero_mul]; exact mul_nonneg (hp _) (Real.exp_pos _).le
     rw [show u' j=u j from if_pos hz]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (hp _)
   next=>rfl
end YM.RemainderComparison.Sleet
