import YM.RG08.Spin.Muffs
/-! # W intertwines rotations. Linear real spacetime.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{c f : Side}{E e r d τ D j t n k m l :ℕ}{R C:ℝ}{F:Labels.Frame G d}{H:Hol G}{S:SectionData F}{s:Signed}{h:1/2≤R}{X Y: BoardU D R G}
section
lemma fFlip (he:Marvel τ X)(hp: Lank X)(hv:Marvel n Y)(hh:Lank Y)(hd:d≤D)(hq:∀ c,Honor s X Y c)(hz:0 < C)(hV:4 ≤ j)(v:Train j):
    let Q:= plaza G C v none; Taste.upside X Q k H F= bankO s F D *ᵥ (Taste.upside Y Q k H F) := by
    intro Q; let U (i r:ℕ):= frisk Q (X i) k r; let V (i r:ℕ) := frisk Q (Y i) k r
    have hQ(i): Honor s U V i:= crest_sig hz hV v he.hem hv.hem hq i
    obtain ⟨B,-,g⟩:=portion G hz hV
    ext1 b; let p:=slot b
    have hG i : Gold (U 0 i):= gold_sum (fun j _=>golden_terraces hz hV (W:=X 0) (fun _=> sober_vetted he) v i j)
    have hG' i:Gold (V 0 i):= gold_sum (fun j _=>golden_terraces hz hV (W:=Y 0) (fun _=> sober_vetted hv) v i j)
    change invest H (U 0 p) b= _
    rw [clerk H b ((hG p).toToute) ((hG' p).toToute) (polished_sum (fun j _=>pol_front (U:=X 0) (g v|>.1) (hp 0) j p)) (polished_sum (fun j _=>pol_front (U:=Y 0) (g v|>.1) (hh 0) j p)) hQ hd,Finset.sum_filter]; unfold mulVec dotProduct; refine Finset.sum_congr rfl fun a _=>?_ ; split_ifs with hg
    · apply congr_arg (bankO s F D b a *·); change invest H (V 0 p) a=invest H (V 0 (slot a)) a; rw [show p=slot a from (sameF hg).2]
    simp only [show bankO s F D b a=0 from if_neg hg, zero_mul]
lemma amber (Y:ReadsU F D R)(hp:Genuine H Y)(ht:Spun s Y)(hd:d≤ D)(he:0<C)(hk:4≤j)(v: Train j):
    let W:=hearth H (plaza G C v none) Y; Commute W (bankO s F D) := by
    intro W; let Z:=fluxO s F D; let P:=plaza G C v none; have hA:= stays hp.toBoards (dilation_O s (D:=D))
    show W*_= _; ext1 i j
    rw [← show Needle.hot Z 0=bankO s F D from ?_] -- force simp
    · rw [← show hearth H P (bureau Y Z) i j=(W*Needle.hot Z 0) i j from flare_out _ _ hp he hk v]
      let b:= bankO s F D
      have hu : Needle.hot Z 0=b:= by ext i j; unfold Z; rw [hot_node,isFlux s i j,if_pos rfl]
      rw [hu]; exact (congr_fun (fFlip (X:=(bureau Y Z j)) (k:=d) (hA.rank j) (hA.paid j) (hp.rank j) (hp.paid j) hd (ht j) he hk v (F:=F)) i).trans (Finset.sum_congr rfl (fun _ _=>rfl))
    ext i j; unfold Z; rw [hot_node,isFlux s i j,if_pos rfl]
variable {T:ChartRatio G}{p:G.ColorIndex}{I:Type}{u:I→Windows}{X:Chain}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{K:Prism G X.kernel g Q E}
variable {hD:d+1≤D}{B:Signals P Q E τ H S h hD}
local notation "Φ" => oven X p T H S (d.le_succ.trans hD) h
theorem bilt (he:Tights B K p T u)(i:Wings u 0)(s:Signed): Commute (Φ i.N i.i) (bankO s F D) := amber _ (he.firs i) (rotated_graph he i s) (d.le_succ.trans hD) X.kernel.penalty_pos (X.adm _) (X.history i.N i.i)
lemma belt (he:Tights B K p T u)(i:Wings u 0)(s: Signed): Commute ((Φ i.N i.i)⁻¹) (bankO s F D):= by
    let W:= Φ i.N i.i; let A:= bankO s F D
    obtain ⟨_,_,F⟩:=portion G X.kernel.penalty_pos (X.adm i.i)
    have h : IsUnit W.det:=(settled_hearth H (he.firs i) (F _|>.1)|>.1) -- ambiguity 
    have he:= (bilt he i s).eq
    calc W⁻¹*A = W⁻¹*A*(W*W⁻¹):= by rw [Matrix.mul_nonsing_inv _ h,mul_one]
         _ = _ := by rw [mul_assoc W⁻¹,← mul_assoc A,← show W*A=A*W from he, ← mul_assoc W⁻¹ (W*A),←mul_assoc W⁻¹ W,Matrix.nonsing_inv_mul _ h,one_mul]
end
end YM.RG08.Spin
