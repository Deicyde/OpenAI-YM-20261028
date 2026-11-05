import YM.RemainderComparison.Solo.Settled

/-!
 # Corresponding setup with SubBudget E. Only inquiries which Odyssey can
 supply; post Rat. Doesn't remove compatibility (full postings addressed,
 can use couplings on their whole purchased stamping). Poll pending ownership Act.
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
open PhysicalNext JointLoad Heir
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G}
lemma atlas (Q:YM.ConnectedActivityE6.Target G P):∃ l:ℕ, ∀ (L:Side), l≤L.val → ∀ (D:Patch), D.Branches P.bind G →
   ∀ (j:ℕ) (ε a:ℝ), 0≤a→0<ε→ a+3*ε≤Q.exp →∀ (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o: ConnectedActivityE6.Target.Order G W),
    ∃ (A a' B C':ℝ)(d v t r F B₀ T K :ℝ→ℝ)(k:ℕ), Rate G L 0 F ∧ ∀ J J' I n P':ℕ, n ≤ j → G.Simple → ∀ (_κ : Chi) (Y:ℝ→ℝ)(i:ℝ→ℕ), Reserve G L Y → Reserve G L (fun x=>(i x:ℝ)) → ∀ (D':Record), D'.ε ≤ 1/4 → 2≤n →∀ (C: Libretto G n),
    ∃ (V V':ℝ→ℝ)(q:ℝ), q<0∧Reserve G L V∧ Rate G L q V'∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D→Stamp T'→∀ (R:Rep G f) (C'':ℝ) (H:Cash W x μ L Q o C'' T' R),
      ∃ N:Captain H j B (d x) (v x) (t x) A a' (r x) (F x) (B₀ x) k χ, Heavy N.conduit ∧ Heroes H N.conduit A (F x) k ∧
      ∀ (ι F:Type) [Fintype ι] [Fintype F] (M:ι→ Lotus.Leaf R)(X' : F→ Site f)(L':ι→ Finset F)(l:ι→ℝ) (σ:ℝ)(E:Set ℕ)(w:ℕ→ℝ) (δ:ℝ),
        Lyric.Scale X' L' M l (i x) σ (Y x) S → radiusCost Q L σ→ Presents R E w δ → δ ≤ incomingE G L x →
        let f₀:=melod M H (rails H N.conduit E w C' (K x)) (T x) k
        Lyric.Paid M H χ N f₀ ∧
        Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ i:Syllable M H z, if Halo.dyed M H E z i ∧ Lyric.notes M H z i≤I then Lyric.Bill M H f₀ z l j i J else 0) (a+ε) (V x*δ) ∧
      ∀ (P'':BudgetPoint), P''.B=radiusB x → P''.threshold=Pressure.temp x → P''.power=P' → P''.power ≤ J → Plays C D' P'' R.p P T' x → Q.halo+5 ≤ J' → ∀ C₀ : ℝ, Release.accepts J' R.p.supportExponent a L → Release.Quotation C P' J' R.p.supportExponent a C₀ →
        Lute.Plented C D' P'' R.p L J' x (gStep R.beta)→ Supply H χ E P'' a ((C₀/L.val+V' x)*δ):= by
   obtain ⟨l,hℓ⟩:= Halo.ramp P Q
   refine ⟨l,fun L hL D hD j ε a ha hε hA χ W hW μ hμ o=>?_⟩
   obtain ⟨A,a',B,C',d,v,t,r,F,B₀,T,K,k,hF,hT,hv,hC⟩:= hℓ L hL D hD j ε (a+ε) (by linarith) hε (by linarith) χ W hW μ hμ o
   refine ⟨A,a',B,C',d,v,t,r,F,B₀,T,K,k,hF,fun J J' I n P' hJ hG κ Y i hY hi D' hb hn C=>?_⟩
   obtain ⟨e,h,eH⟩:= Brim.scored G hG P L D hD P' n C D' hb hn χ κ W o a J' ha
   obtain ⟨V,S',q,hq,hV,hP,hZ⟩:= hC I J Y i hY hi
   let u:=max q (-(1/2:ℝ))
   refine ⟨V,fun x=> |e x| + (V x*S' x+Real.exp (-ε*radiusB x)*V x),u,max_lt hq (by norm_num),hV,(by
      apply ((h.compare (v:=fun x=> |e x|) (Eventually.of_forall (fun x=> (abs_abs _).le))).weaken (le_max_right ..)).add
      apply Rate.add
      · exact (hV.rate.mul hP.rate).weaken (by rw [zero_add]; exact le_max_left ..)
      have hk : Rate G L u (fun x=> Real.exp (-ε*radiusB x)) := Rate.compare (Rate.cutoff hε) (Eventually.of_forall (fun x=> by
         rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; refine Real.exp_monotone (mul_le_mul_of_nonpos_left (show (till x:ℝ) ≤ radiusB x from by exact_mod_cast Nat.div_le_self ..) (neg_nonpos.mpr hε.le))))
      exact (hk.mul hV.rate).weaken (le_of_eq (add_zero _))),?_⟩
   filter_upwards [hZ,eH] with x hX he c f S T' hS hT R C'' H
   obtain ⟨N,hΞ,hs,hM⟩:= hX c f S T' hS hT R C'' H
   refine ⟨N,hΞ,hs,?_⟩; intro ι F _ _ M X' L' l σ E w δ h hL hp hv f₀
   obtain ⟨hq,hh⟩:= hM ι _ M X' L' l _ E _ δ h hL hp hv
   refine ⟨hq,?_,fun P'' hP' ht hb hΙ hW hJ' C₀ hA hC hB=>?_⟩
   · convert! hh 0 using 1; swap; · rw [pow_zero,mul_one]
     ext z; apply Finset.sum_congr rfl; intro i hi
     by_cases hp:Halo.dyed M H E z i
     · have hz:1≤Halo.gross M H z i:=by
         obtain ⟨a,p,-,hH⟩:= hp; exact le_trans (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨p,hH⟩)) (single_le_sum (f:=fun a=>((z.2 a).val\(i a).reach).card) (fun j _=> Nat.zero_le _) (mem_univ a))
       simp [f₀,hp,hz]
     simp [hp] -- edit
   obtain hz:= he c f S T' hS H.laws.data.funds R Q _ _ H P'' hP' hb hW hJ' C₀ hA hC hB j hJ _ _ _ _ _ _ _ _ _ k N E w δ hp hv
   convert solo M H χ N l E w f₀ P'' ht hP' (hW.rehearsed.test.le.trans hJ) hΙ hp hz hq h.currency (Eq.refl _) hε.le hh using 1; ring
end YM.RemainderComparison.Solo
