import YM.RG08.Yamen.Plum

/-! # Boundary assets paid at level scale. True Wilson top, varying jobs. !-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}{G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{W:Rate.Stair O}{E e r:ℕ}
variable (K:Wheelhouse a E W)(L:Supplies F P Z)
variable {N:O→ℕ}(hi:∀ i:O,W.top i ≤ N i)
local notation "Q"=>Yamen.charter P X Z K
local notation "S"=>Yamen.Act F X hg Z K N hi L
local notation "J"=> Yamen.caliph F X hg Z K N hi L

private lemma top_cost (G:Gauge)(e r:ℕ): ∃ C:ℝ,0 ≤ C ∧ ∀ σ : ℝ, σ ≤ 1 →Held (carpet _) σ C (Yamen.top G r e):=by
 obtain ⟨C,hc,H⟩:=Crown.earned (σ:=1) G (RG08.Mount.rank r) (RG08.Mount.stick r)
 refine ⟨C,zero_le_one.trans hc,fun σ ht=>?_⟩;unfold Yamen.top;split;exact H.mono ht le_rfl (fun _=>le_rfl); exact zero_held
private lemma top_width (e r:ℕ)(i:ℕ):(lamp P X a i).coats e r ≤1:= ((lamp P X a i).tag e r).2.1.trans ((honesty_small G P X a.clock.kernel (a.clock.J i) e).trans (trod_below ..))
-- kinetic after normalization
lemma cargo {i N:ℕ}(h:i<N) :fed F P X hg Z N i 0 0= Yamen.base P X a i (F.H N i):=by
 rw [mint_step h,mint,Nacre.send,Nacre.size];simp only [Nacre.square,zero_add,Finset.range_one,sum_singleton,due_self,one_smul];rfl
lemma realism (hE:Yamen.Funds P X Z a W): Lapel (r:=0) (kiosk W) (fun i=>apron (Q).yard 0 0 i.x i.m) fun i=>(J).current i.x i.m 0 0:=by
 obtain ⟨U,hU,HU⟩:=top_cost G 0 0
 refine ⟨_,(kiosk W).hear _ _ ((kiosk W).steady U hU) hE,fun i=>?_⟩
 let n:= i.m;let j:=a.clock.J n;let p:= a.clock.J (n+1)
 let s:= gift P X Z a n
 have hp:=stamped G P X a.clock.kernel Z (RG08.Supplies.stone a i.m)
 have hb : 1 ≤ s:=hp.pos
 change Held _ ((lamp P X a n).coats 0 0) (U+s) (fed F P X hg Z (N i.x) n 0 0)
 rcases lt_or_eq_of_le (station _ hi i) with h|h
 · rw [cargo hg h]; apply (veils (X:=X) L.housed (N i.x) i.m hg h.le (fun b=> L.herald _ _ _ h.le)).2.mono le_rfl ?_ (fun _=>le_rfl)
   exact (hp.base j (show j ≤ (RG08.Supplies.stone a i.m).J from a.fits.mono (by omega : i.m ≤ i.m+1))).trans (le_add_of_nonneg_left hU)
 change i.m=N i.x at h
 unfold n;rw [h,top_eq]; exact (HU _ (top_width _ _ _)).mono le_rfl (by linarith) (fun _=>le_rfl)

lemma perspective (hE:Yamen.Funds P X Z a W): Lapel (r:=0) (turnstile W) (coats (Q).warp 0 0) (S).top:=by
 refine ⟨_, (show (turnstile W).Good (pay P X Z a) from lowString.golf _ hE),fun i=> ?_⟩
 have hi := (veils (X:=X) L.housed (N i.x) i.m hg (shoulders _ hi i).le (fun b=>L.herald _ _ _ (shoulders _ hi i).le)).2
 refine hi.mono le_rfl ((postpaid (X:=X) (Z:=Z) K i).base _ (a.fits.mono (show i.m ≤ i.m+1 by omega))) (fun _=>le_rfl)

def civic (hE:Yamen.Funds P X Z a W)(hM:Bill G P X a)(h:∀ e r,e ≤ E→Live r e→0<e→∃ p,(kiosk W).Good p ∧ ∀ i:Haven W,i.m=W.top i.x→Held (carpet _) (apron (Q).yard e r i.x i.m) (p i) ((J).current i.x i.m r e)) :Vow hg E J where
 tuition _ _ he hT hf:=realmap hg K L hM hE hi he hT hf
 agreement :=receipts F X hg Z K N hi L
 base:=realism hg K L hi hE
 baseC:=perspective hg K L hi hE
 trench:=h

def starter (hE:Yamen.Funds P X Z a W)(hM:Bill G P X a): Vow hg E (Yamen.caliph F X hg Z K W.top (fun _=>le_rfl) L):=by
 apply civic hg K L (X:=X) _ hE hM
 intro e r _ _ _
 obtain ⟨C,hc,H⟩:=top_cost G e r
 refine ⟨_,(kiosk W).steady C hc,fun i hi=>?_⟩
 change Held _ ((lamp P X a i.m).coats e r) C (fed _ _ _ _ _ _ _ _ _); rw [hi,top_eq];exact H _ (top_width ..)
end YM.RG08.Yamen
