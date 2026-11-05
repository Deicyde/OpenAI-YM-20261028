import YM.RG08.Plot.Hearth
/-!
# Storm decomposition of full Wilson product read. Before resetting/reporting. Transfer of all differential paths charged in Sect. `Attic`.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type}{r n k E D τ j b t N:ℕ}{G:Gauge}{L:Side}{R:ℝ}{X:Chain}{ν:G.ColorIndex}{D':ChartRatio G}
variable {Φ:BoardU D R G}{V:I→ℕ→ BoardU D R G}{p:List I}{a h:I→ℕ}{x:E4}{φ:I→ Profile D}
-- Kolping predicate on fine $k$..N. Ambient supplied. Caps proof later. Marker load `N` not reused.
structure Scenes (X:Chain)(ν:G.ColorIndex)(D':ChartRatio G)(K N:ℕ)(p:List I)(a h:I→ℕ)(V:I→ℕ→BoardU D R G): Prop where
   prices i : K≤ i→ i < N → Fair (dance X ν D' N i)
   paysR: 1/2 ≤ R
   heads z (hz:z∈p) i : K ≤ i→ i ≤ N→ Marvel (a z) (V z i)
   stepL z (hz:z∈p) i : K≤ i→ i < N→ V z i= Needle.push (dance X ν D' N i) (a z) (h z) (V z (i+1))
variable (X ν D')
def marchFi (K:ℕ)(x:E4)(h:ℕ)(g:Profile D)(V:ℕ→ BoardU D R G)(i:ℕ): Tale G:= collect X h K i g x (V i)
def marchFull (K:ℕ)(x:E4)(p:List I)(h:I→ℕ)(φ:I→ Profile D)(V:I→ℕ→BoardU D R G)(i:ℕ): Tale G:= castF (fun j=> marchFi X K x (h j) (φ j) (V j) i) p
variable {X ν D'} {k s i:ℕ}
variable (v:Scenes X ν D' k N p a h V)
local notation "Γ" => dance X ν D' N
section narrative
include v
lemma costs_f (z)(hz:z∈p)(i)(hp:k ≤ i)(he:i ≤ N)(x:E4)(φ:Profile D): Stone (a z) (marchFi X k x (h z) φ (V z) i):= stem_for φ x _ _ _ (v.heads z hz i hp he)
lemma tides_s (he:k ≤ i)(hx:i < N)(z)(hz:z∈p)(x:E4)(φ:Profile D): marchFi X k x (h z) φ (V z) i=inscribed (a z) (Γ i) 0 (marchFi X k x (h z) φ (V z) (i+1)):= by
   unfold marchFi; rw [v.stepL z hz _ he hx]; exact (occurs v.paysR (v.heads _ hz _ (he.trans (Nat.le_succ _)) hx) (v.prices _ he hx)).symm
lemma cost_full (he:k ≤ i)(hx:i ≤ N)(x:E4)(φ:I→Profile D): Stone (loadᵣ a p) (marchFull X k x p h φ V i):= stone_cast fun z hz=>costs_f v z hz i he hx x _
end narrative
-- discrepancy exact all products, in origin representation
variable (X ν D')
def extraD (K N:ℕ)(x:E4)(p:List I)(a h:I→ℕ)(φ:I→Profile D)(V:I→ℕ→BoardU D R G)(i:ℕ) := inscribed (loadᵣ a p) (dance X ν D' N i) 0 (marchFull X K x p h φ V (i+1))-marchFull X K x p h φ V i
def crystal (K N:ℕ)(x:E4)(p:List I)(a h:I→ℕ)(φ:I→Profile D)(V:I→ℕ→BoardU D R G) (i j:ℕ):= dustP X ν D' N i (loadᵣ a p) j (extraD X ν D' K N x p a h φ V i)
-- tested and restored $F_i$
def waveProduct (K N:ℕ)(x:E4)(p:List I)(a h:I→ℕ)(φ:I→Profile D)(V:I→ℕ→BoardU D R G)(i:ℕ):= dustP X ν D' N N (loadᵣ a p) i (marchFull X K x p h φ V N)
variable {X ν D'}
local notation "✽" => extraD X ν D' k N x p a h φ V
local notation "☐" => marchFull X k x p h φ V
local notation "★" => crystal X ν D' k N x p a h φ V
lemma full_eq {F H:I→ Tale G}(hx:∀ i∈p,F i=H i):castF F p=castF H p:= by
    induction p with
    | nil=>rfl
    | cons i p ih=>change gust _ (castF F p)=gust _ (castF H p); exact congr_arg₂ gust (hx _ (by simp)) (ih fun v hv=>hx v (by simp [hv]))
section story
include v
lemma innate (he:k ≤ i)(hx:i < N)(x:E4)(φ:I→ Profile D): Stone (loadᵣ a p) (extraD X ν D' k N x p a h φ V i) := Stone.less (inscribe_law _ (v.prices _ he hx) (cost_full v (he.trans (Nat.le_succ _)) hx x φ)) (cost_full v he hx.le x φ)
lemma drift_moves (he:k ≤ i)(hx:i < N): Town.season (-arcT X k i x) (✽ i)= shout p h a (Γ i) φ k x (fun j=> V j (i+1)):= by
    let Q:= shrinkP X k i x; let y:=arcT X k i x; let W:=arcT X k (i+1) x
    let F z:= marchFi X k x (h z) (φ z) (V z) (i+1)
    let U:= castF F p
    have hh : Lattice.lift Q + -W=(X.S.block i).val • (-y)+ Lattice.lift (0:Site (X.S.block i)):= by unfold Q; rw [arena,nil_root,smul_neg]; unfold W y; abel
    have hz i (h':i∈p):= tides_s v he hx i h' x (φ i)
    have hc z (hz':z∈p) : inscribed (a z) (Γ i) Q (burned (h z) k (i+1) (φ z) X x (V z (i+1)))=Town.season (-y) (marchFi X k x (h z) (φ z) (V z) i):= by -- shadow
       rw [hz z hz']; apply order_moves (_: Stone (a z) (F z)) (v.prices _ he hx) hh; exact costs_f v z hz' (i+1) (by omega) hx x _
    have hS:= cost_full v (he.trans (Nat.le_succ _)) hx x φ
    change Town.season (-y) (inscribed (loadᵣ a p) (Γ i) 0 U-☐ i) = _
    rw [show Town.season (-y) (inscribed (loadᵣ a p) (Γ i) 0 U-☐ i)=Town.season (-y) (inscribed (loadᵣ a p) (Γ i) 0 U)-Town.season (-y) (☐ i) from rfl]
    unfold marchFull; unfold shout jamT; refine congr_arg₂ (·-·) ?_ ?_
    · rw [←order_moves (q:=Q) (h:=(_ : Stone (loadᵣ a p) U)) (hk:=v.prices _ he hx) (he:=hh)]; swap; · exact hS
      unfold U; rw [space_for (A:=a) (-W) (U:=F) (fun z hz=> costs_f (φ:=φ z) v z hz (i+1) (by omega) hx x)]; rfl
    rw [space_for (A:=a) (-y) (fun z hz=> costs_f v z hz i he hx.le x _)]; apply Eq.symm; exact full_eq hc
lemma dust_rides (he:k ≤ i)(ht:i≤ b)(hx:b < N): Stone (loadᵣ a p) (★ b i):= by
    induction ht using Nat.decreasingInduction with
    | self=> unfold crystal; rw [dust_top]; exact innate v he hx ..
    | of_succ i hi ih=>
       unfold crystal; rw [dust_step _ _ _ _ _ _ _ _ hi]; exact inscribe_law _ (v.prices _ he (hi.trans hx)) (ih (by omega))
theorem serve (he:k ≤ i)(hv:i≤ N): waveProduct X ν D' k N x p a h φ V i=☐ i+ ∑ j ∈ Ico i N, ★ j i := by
   induction hv using Nat.decreasingInduction with
   | self=> unfold waveProduct; simp
   | of_succ i hv ih=>
     have hδ:=v.prices i he hv
     have hx j (hj:j∈Ico (i+1) N): Stone (loadᵣ a p) (★ j (i+1)):= dust_rides v (he.trans (Nat.le_succ _)) (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
     let F := ☐ (i+1); let Y:= inscribed (loadᵣ a p) (Γ i) 0; have hf : Stone (loadᵣ a p) F:= cost_full v (he.trans (Nat.le_succ _)) hv x φ
     rw [waveProduct,dust_step _ _ _ _ _ _ _ _ hv]; change Y (waveProduct _ _ _ _ _ _ _ _ _ _ _ (i+1))=_; rw [ih (he.trans (Nat.le_succ _))]
     change Y (F+∑ j∈ Ico _ _, ★ j (i+1))= _
     unfold Y; rw [inscription_add _ hf (Stone.group _ _ hx) hδ, inscript_list _ _ _ hx hδ, ← Finset.insert_Ico_succ_left_eq_Ico hv] -- name
     let T:=∑ j∈Ico (i+1) N,★ j i
     rw [sum_insert, show ∑ j∈Ico (i+1) N, Y (★ j (i+1)) = T from sum_congr rfl fun j hj=>Eq.symm (dust_step _ _ _ _ _ _ _ _ (mem_Ico.mp hj).1)] -- Y
     swap; · simp
     rw [show ★ i i= ✽ i from dust_top ..]; change Y F + _= ☐ i+(Y F-☐ i+_); abel
end story
end YM.RG08.Plot
