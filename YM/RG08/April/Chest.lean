import YM.RG08.April.Fascia
/-! # Linear absorbers on Exchange.Here pairs of scalar entries.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Lattice Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow
open scoped Classical Matrix BigOperators PowerSeries Topology
variable {X Z:Type}{G:Gauge}{W:Rate.Stair X}{D d p l e n k r:ℕ}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover
-- assume bound at all Haven via Alloc. Generic get Fee recurrence. Use arrays f:Haven→ℝ≥0
private lemma cost (p:Haven W→ℝ)(V:Haven W→ℝ)(U:Run W→ℝ)(h:∀ i,0≤p i)(hV:(kiosk W).Good V)(hU:(turnstile W).Good U)(ht:∀ i:Haven W,i.m=W.top i.x→p i ≤ V i)(hi:∀ i:Run W,p i.low ≤ p i.high/Real.sqrt (W.length i.x i.m)+U i):
 (kiosk W).Good p:=by
 let f:=Mason.wide V;let g:=Mason.wide U
 let F(x:X)(i:ℕ):= if i=W.top x then f x i else g x i
 have H:W.Poly F:= ((show W.Poly f from hV).add (show W.Poly g from hU)).mono fun x i hi=>by
    have ha:0≤ f x i:=Rate.Stair.Poly.nonneg hV hi;have hu:0≤g x i:=Rate.Stair.Poly.nonneg hU hi; dsimp only [F];split<;> constructor <;>linarith
 refine poly_solve (θ:=1/2) (by norm_num) (fun x n hi=>by unfold wide;rw [dif_pos hi];exact h _) H ?_
 intro x i hK;by_cases hx:i < W.top x
 · let j:Run W:=⟨x,i,hK,hx⟩
   have hs:active W x i:= j.admit
   have hg:W.Here x (i+1):=j.high.admit
   unfold Rate.Stair.stepOnly F g
   rw [if_pos hx,if_neg hx.ne];simp only [Mason.wide,dif_pos hK,dif_pos hg,dif_pos hs]
   change p j.low≤ p j.high* _+U j; rw [←sqrt_drop j];exact hi j
 have hp:i=W.top x:=le_antisymm hK.2 (by omega)
 unfold Rate.Stair.stepOnly F f;rw [if_neg hx,if_pos hp,zero_add];unfold wide;rw [dif_pos hK,dif_pos hK];exact ht (⟨x,i,hK⟩:Haven W) hp
private lemma costF (p:Haven W→ℝ)(V:Haven W→ℝ)(U:Run W→ℝ)(h:∀ i,0≤p i)(hV:(kiosk W).Good V)(hU:(turnstile W).cheap U)(ht:∀ i:Haven W,i.m=W.top i.x→p i ≤ V i)(hi:∀ i:Run W,p i.low ≤ p i.high/Real.sqrt (W.length i.x i.m)+U i):
 (kiosk W).cheap p:=by
 let f:=Mason.wide V;let g:=Mason.wide U
 let F(x:X)(i:ℕ):= if i=W.top x then f x i else 0
 have hP:W.Poly F:= (show W.Poly f from hV).mono fun x i hx=>by
    have ha:0≤ f x i:=Rate.Stair.Poly.nonneg hV hx; dsimp only [F];split<;> simp [ha]
 have H:W.Fade F:= Rate.Stair.Fade.of_top hP fun x i h hx=> if_neg (by omega)
 refine fade_solve (θ:=1/2) (by norm_num) (fun x n hi=>by unfold wide;rw [dif_pos hi];exact h _) (H.add (show W.Fade g from hU)) ?_
 intro x i hK;by_cases hx:i < W.top x
 · let j:Run W:=⟨x,i,hK,hx⟩
   have hs:active W x i:= j.admit; have hg:W.Here x (i+1):=j.high.admit
   change wide p _ _≤ _+(F x i+g x i); unfold Rate.Stair.stepOnly F g
   rw [if_pos hx,if_neg hx.ne,zero_add];simp only [Mason.wide,dif_pos hK,dif_pos hg,dif_pos hs]
   change p j.low≤ p j.high* _+U j; rw [←sqrt_drop j];exact hi j
 have hp:i=W.top x:=le_antisymm hK.2 (by omega)
 change _≤_+(F _ _+g _ _)
 have hf:0≤g x i:=Rate.Stair.Fade.nonneg hU hK
 unfold Rate.Stair.stepOnly F f;rw [if_neg hx,if_pos hp,zero_add];unfold wide;rw [dif_pos hK,dif_pos hK];exact (ht (⟨x,i,hK⟩:Haven W) hp).trans (le_add_of_nonneg_right hf)

-- Sings at multiple simultaneous columns (max sup in finite nonneg sets) one gain independent of column count. Need already expenditure complete to price with q.Blue; width and linear. Choose p minimum aesthetic using `fold max 0`. then application.
variable {I:Type}[Fintype I]{σ:Haven W→ℝ}{h:∀ i,0<σ i}{T:Haven W→I→Pack n (Ed G Cover)}
def sizes (σ:Haven W→ℝ)(h:∀ i,0<σ i)(D:ℕ)(T:Haven W→I→Pack n E)(i:Haven W):=Finset.fold max 0 (fun k=>Jetty.hymn Δ D (h i) (T i k)) univ
lemma complete_locus (hl:∀ i j,∃ p,Sings Δ D (h i) (T i j) p):∀ i,0≤ sizes σ h D T i ∧ ∀ j,Sings Δ D (h i) (T i j) (sizes σ h D T i):=by
 intro i;refine ⟨(le_fold_max _).mpr (Or.inl le_rfl), fun j=>?_⟩
 obtain ⟨p,hp⟩:=hl i j;exact hp.cost.mono le_rfl le_rfl (fun _=>le_rfl) ((le_fold_max _).mpr (Or.inr ⟨j,mem_univ _,le_rfl⟩))
lemma locus_le {x:Haven W}{p:ℝ}(hx:0≤p)(hc:∀ j,Sings Δ D (h x) (T x j) p):sizes σ h D T x≤p:= (fold_max_le _).mpr ⟨hx,fun i _=> (hc i).hymn_le hx⟩

lemma drawers {q:Haven W→ℝ}{p:Run W→ℝ}(hq:(kiosk W).Good q)(hp:(turnstile W).Good p)(hl:∀ i j,∃ p,Sings Δ D (h i) (T i j) p)
 (hs:∀ (i:Haven W),i.m=W.top i.x→∀ j,Sings Δ D (h i) (T i j) (q i))
 (hx:∀ (i:Run W)(r:ℝ),0≤r→(∀ j,Sings Δ D (h i.high) (T i.high j) r)→∀ j,Sings Δ D (h i.low) (T i.low j) (r/Real.sqrt (W.length i.x i.m)+p i)):∃ f,(kiosk W).Good f ∧ ∀ i j,Sings Δ D (h i) (T i j) (f i):=by
 refine ⟨sizes σ h D T,cost _ q p (fun i=> (complete_locus hl i).1) hq hp (fun i hi=>locus_le ((kiosk W).safe _ hq _) (hs i hi)) (fun i=> locus_le (add_nonneg (div_nonneg (complete_locus hl i.high).1 (Real.sqrt_nonneg _)) ((turnstile W).safe _ hp _)) (hx i _ (complete_locus hl i.high).1 (complete_locus hl i.high).2)),fun i=> (complete_locus hl i).2⟩
lemma drawer {q:Haven W→ℝ}{p:Run W→ℝ}(hq:(kiosk W).Good q)(hp:(turnstile W).cheap p)(hl:∀ i j,∃ p,Sings Δ D (h i) (T i j) p)
 (hs:∀ (i:Haven W),i.m=W.top i.x→∀ j,Sings Δ D (h i) (T i j) (q i))
 (hx:∀ (i:Run W)(r:ℝ),0≤r→(∀ j,Sings Δ D (h i.high) (T i.high j) r)→∀ j,Sings Δ D (h i.low) (T i.low j) (r/Real.sqrt (W.length i.x i.m)+p i)):∃ f,(kiosk W).cheap f ∧ ∀ i j,Sings Δ D (h i) (T i j) (f i):=by
 refine ⟨sizes σ h D T,costF _ q p (fun i=> (complete_locus hl i).1) hq hp (fun i hi=>locus_le ((kiosk W).safe _ hq _) (hs i hi)) (fun i=> locus_le (add_nonneg (div_nonneg (complete_locus hl i.high).1 (Real.sqrt_nonneg _)) (tiny _ hp _)) (hx i _ (complete_locus hl i.high).1 (complete_locus hl i.high).2)),fun i=> (complete_locus hl i).2⟩
end YM.RG08.April
