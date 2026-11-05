import YM.RG08.Harvest.Trad
/-!
# Continuous center representation through any finite step
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type} {u:I→Windows}{n k j m N i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D t:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}
variable {W:Type}[TopologicalSpace W]{b:J→Dial u}{a:M→ℕ}{p:List M}
section operations
lemma preserve_dust {F:W→ Tale G}(h:Via G t F) (hv: i ≤ N)(hp:∀ k,i ≤ k→ k < N → Fair (dance X ν D' m k)): Via G t (fun w=> dustP X ν D' m N t i (F w)):= by
   induction hv using Nat.decreasingInduction with
   | self=> simp_rw [dust_top]; exact h
   | of_succ i hk ih=> simp_rw [fun x:W=>dust_step X ν D' m i N t (F x) hk]; exact (ih fun k he=>hp k ((Nat.le_succ _).trans he)).inscription 0 (hp i le_rfl hk)
lemma off_stance {φ':ReadsU F D R}(ht:Boards φ')(s:Native (Letter F))(b: Letter F) :
    let A:=fund (φ' b) (s b); Marvel d A ∧ Lank A := by -- binder
   let x:=fun j:Letter F=> if j=b then s j else 0
   rw [show fund (φ' b) (s b)=edgeBook φ' x from ?_]; · intro; exact edge_crew φ' x ht le_rfl
   unfold edgeBook; rw [sum_eq_single b]; rw [show x b=_ from if_pos rfl]
   intro i _ hi; rw [show x i=0 from if_neg hi]; funext k j; unfold fund adapt; simp only [map_zero,zero_smul,sum_const_zero]
   simp
lemma book_incomes (H:Hol G)(Ω:SectionData F)(hp:Ω.Sound H)(hm: Bid.pop Ω)(hd:d≤D)(hR:1/2≤R)(g:Exam D)(w:W→ E4)(hw:Continuous w)(x:E4)(p:Cover)(α:ℝ)(s:Native (Letter F)):
   let V := fun b:Letter F=> startU Ω b hd ((by norm_num : (0:ℝ) ≤1/2).trans hR); let Z i:= exteriorP g α (w i) p
   Via G d (fun i=> ringU (Z i) (edgeBook V s)) := by
   intro V Z
   have ht: ∀ b:Letter F, Continuous (fun i=> chant b hd ((by norm_num : (0:ℝ)≤1/2).trans hR) (Z i)) := by
     intro b
     let K:=cashT b.test; let S':=fun i=> iteratedFDeriv ℝ K g.val (stud α (w i) p)
     have hK:K≤D:=(le_trans (Nat.le_add_left ..) b.bill).trans hd
     have hs: Continuous S':=((Scores.score D g).continuous_iteratedFDeriv (Nat.cast_le.mpr hK)).comp (continuous_const.sub hw)
     let v:= YM.basis ∘ needleT b.test
     change Continuous (fun i=> iteratedFDeriv ℝ K (Z i).val 0 v)
     simp only [Z,exteriorP,fun i:E4=> Pages.facades (stud α i p) α g K hK (0:E4),smul_zero,add_zero]; exact ((ContinuousMultilinearMap.apply ℝ _ ℝ v).continuous.comp (hs.const_smul (α^K))) -- multilinear
   let χ (b: Letter F) i:=ringU (Z i) (fund (V b) (s b));
   rw [show (fun i=> ringU (Z i) (edgeBook V s)) = (fun i=>∑ b, χ b i) from funext fun i=>?_]; swap
   · funext j r; unfold χ ringU; rw [Finset.sum_apply,Finset.sum_apply]; unfold edgeBook; rw [Finset.sum_apply,Finset.sum_apply, graft]; -- z explicit problem
   have hv:= section_genuine H Ω hp hm hd hR
   refine Via.sum (F:=χ) _ (fun b hb=>?_)
   let g' i:= chant b hd ((by norm_num : (0:ℝ) ≤1/2).trans hR) (Z i); let Q:= ringU (coinsT D b.test) (fund (V b) (s b)); obtain ⟨hA,hQ⟩:= off_stance (φ':=V) hv.toBoards s b
   have he i: χ b i= g' i • Q := by
      have he(j r): plug (Z i) R ∘ V b j r= g' i • (plug (coinsT D b.test) R ∘ V b j r):= by
         have hA:0≤R:= (by norm_num : (0:ℝ)≤1/2).trans hR; unfold V; simp_rw [echo_start]; rw [show chant b hd hA (coinsT D b.test)=1 from (pointed (p:=b.test) (q:=b.test) ((le_trans (Nat.le_add_left (cashT b.test) _) b.bill).trans hd) hA).trans (if_pos rfl)] -- fix syntax
         · split <;> simp [g']
      ext1 j; ext1 r; funext b'
      change ringU (Z i) _ j r b'=g' i*ringU _ _ _ _ b'; unfold ringU fund adapt; simp only [Finset.sum_apply, Function.comp_apply, _root_.map_sum, Pi.smul_apply, _root_.map_smul, Finset.mul_sum]; refine sum_congr rfl ?_; intro k hk; rw [footing (mem_range_succ_iff.mp hk)]; change coeff k (s b)*(plug (Z i) R∘V b (j-k) r) b'=g' i*(coeff k (s b)* _); rw [he,mul_left_comm]; rfl
   rw [show χ b= (fun i=> g' i • Q) from funext he]; exact Via.head _ (Stone.graph hA _) (fun i j=> polished_fun (hQ i j) _) _ (ht b)
end operations
end YM.RG08.Harvest
