import YM.RG08.Mason.Faith
import YM.RG08.Rate.Ascent
/-! # Produce analytic reserves through arbitrarily many actual steps from the step receipts
 on an Exchange. Solves bounds rather than requiring finiteness of ledger's entries upfront.
-/
noncomputable section
namespace YM.RG08.Mason
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {X:Type}{W:Rate.Stair X}{G:Gauge}{r:ℕ}
private def zoom (W:Rate.Stair X)(U V:Rate.Stair.Array X) (x:X):ℕ→ℝ
| 0=>V x (W.top x)
| n+1=>let i:= W.top x-(n+1);zoom W U V x n * W.drop (1/2) x i + U x i
private def tabbed (W:Rate.Stair X)(U V:Rate.Stair.Array X)(x:X)(i:ℕ):=zoom W U V x (W.top x - i)
private lemma tab_top (U V:Rate.Stair.Array X)(x:X):tabbed W U V x (W.top x) = V x (W.top x):=by rw [tabbed,Nat.sub_self,zoom]
private lemma tab (U V:Rate.Stair.Array X)(x:Run W):tabbed W U V x.x x.m =tabbed W U V x.x (x.m+1) * W.drop (1/2) x.x x.m + U x.x x.m:=by
 have h:=x.admit.2; unfold tabbed; nth_rw 1 [show W.top x.x-x.m=W.top x.x-(x.m+1)+1 by omega]; rw [zoom,show W.top x.x-(W.top x.x-(x.m+1)+1)=x.m by omega]
-- note additive multiplication convention
private lemma downhill {θ:X→ℕ→Prop}(h:∀ i:Haven W,i.m=W.top i.x→ θ i.x i.m)(ht:∀ i: Run W,θ i.x (i.m+1)→ θ i.x i.m)(i:Haven W): θ i.x i.m:=by
 generalize he:W.top i.x-i.m=n
 induction n generalizing i with
 | zero=>apply h; have hi:= i.admit.2;omega
 | succ n hi=>
    let x:Run W:=⟨i.x,i.m,i.admit,by omega⟩
    apply ht x; exact hi x.high (by change W.top i.x-(i.m+1)=_;omega)

lemma sqrt_drop (x:Run W)(p:ℝ):p/Real.sqrt (W.length x.x x.m)=p*W.drop (1/2) x.x x.m:=by
 rw [Real.sqrt_eq_rpow,div_eq_mul_inv, ←Real.rpow_neg (show 0≤W.length x.x x.m from le_trans (by norm_num) (W.length_large ..)),W.drop_length]

-- predicate solved on HERE universe. p-array horizon independent of s cut. slot count f x i fixed.
theorem ribs {F:X→ℕ→Gird G r}{w:X→ℕ→ℝ}{U:Run W→ℝ}{V:Haven W→ℝ}
 (hV: (kiosk W).Good V)(hU:(turnstile W).Good U)
 (h:∀ i:Haven W,i.m=W.top i.x→ Held (carpet _) (w i.x i.m) (V i) (F i.x i.m))
 (ht:∀ (x:Run W)(p:ℝ),0≤p→ Held (carpet _) (w x.x (x.m+1)) p (F x.x (x.m+1)) → Held (carpet _) (w x.x x.m) (p/Real.sqrt (W.length x.x x.m)+U x) (F x.x x.m)):
    Lapel (kiosk W) (fun i=>w i.x i.m) (fun i=> F i.x i.m):=by
 let f:=wide U;let g:=wide V; let q:=tabbed W f g
 have hh:=downhill (W:=W) (θ:=fun i j=>0≤q i j ∧ Held (carpet _) (w i j) (q i j) (F i j)) ?hM ?hT
 case hM=> intro i hi;rw [show q i.x i.m = V i from (show tabbed W f g i.x i.m= V i from by
            have he:q i.x (W.top i.x)=g i.x (W.top i.x):=tab_top f g i.x;change q i.x i.m = _;rw [←hi] at he;rw [he];unfold g wide;rw [dif_pos i.admit])];exact ⟨(kiosk W).safe _ hV i,h i hi⟩
 case hT=> intro i hi;rw [show q i.x i.m=_ from tab f g i,show f i.x i.m=U i from dif_pos i.admit,←sqrt_drop i]; exact ⟨add_nonneg (div_nonneg hi.1 (Real.sqrt_nonneg _)) ((turnstile W).safe _ hU _),ht i _ hi.1 hi.2⟩
 let P(i:X)(k:ℕ):=if W.top i=k then g i k else f i k
 have hp:W.Poly P:= ((show W.Poly g from hV).add (show W.Poly f from hU)).mono fun x i hi=> by
    dsimp [P];have he:=Rate.Stair.Poly.nonneg hV hi;have ht:=Rate.Stair.Poly.nonneg hU hi; change 0 ≤ g _ _ at he;change 0 ≤ f _ _ at ht;split<;> constructor <;> linarith
 have hq:W.Poly q:= poly_solve (θ:=1/2) (by norm_num) (fun i n h=> (hh ⟨i,n,h⟩).1) hp (fun x i hi=>by
    unfold Stair.stepOnly P; split_ifs with hj hh <;> first | omega | skip
    · exact le_of_eq (tab f g ⟨x,i,hi,hj⟩)
    all_goals have ht: i=W.top x:=by have h:=hi.2;omega
    all_goals first|omega| (rw [ht,zero_add,show q x (W.top x)=_ from tab_top f g x])) -- if branches
 refine ⟨fun i=>q i.x i.m,hq.mono (fun x k hi=>?_),fun i=>(hh i).2⟩ -- need expected kiosk def
 rw [wide,dif_pos hi];exact ⟨(hh ⟨x,k,hi⟩).1,le_rfl⟩

theorem cruises {F A:X→ℕ→Gird G r}{w:X→ℕ→ℝ}{U:Run W→ℝ}{V:Haven W→ℝ}
 (hV: (kiosk W).Good V)(hU:(turnstile W).cheap U)
 (h:∀ i:Haven W,i.m=W.top i.x→ Held (carpet _) (w i.x i.m) (V i) (F i.x i.m-A i.x i.m))
 (ht:∀ (x:Run W)(p:ℝ),0≤p→ Held (carpet _) (w x.x (x.m+1)) p (F x.x (x.m+1)-A x.x (x.m+1)) → Held (carpet _) (w x.x x.m) (p/Real.sqrt (W.length x.x x.m)+U x) (F x.x x.m-A x.x x.m)):
    Wave (kiosk W) (fun i=>w i.x i.m) (fun i=> F i.x i.m) fun i=> A i.x i.m:=by
 let f:=wide U;let g:=wide V; let q:=tabbed W f g
 have hh:=downhill (W:=W) (θ:=fun i j=>0≤q i j ∧ Held (carpet _) (w i j) (q i j) (F i j-A i j)) ?hM ?hT
 case hM=> intro i hi;rw [show q i.x i.m = V i from (show tabbed W f g i.x i.m= V i from by
            have he:q i.x (W.top i.x)=g i.x (W.top i.x):=tab_top f g i.x;change q i.x i.m = _;rw [←hi] at he;rw [he];unfold g wide;rw [dif_pos i.admit])];exact ⟨(kiosk W).safe _ hV i,h i hi⟩
 case hT=> intro i hi;rw [show q i.x i.m=_ from tab f g i,show f i.x i.m=U i from dif_pos i.admit,←sqrt_drop i]; exact ⟨add_nonneg (div_nonneg hi.1 (Real.sqrt_nonneg _)) (tiny _ hU _),ht i _ hi.1 hi.2⟩
 let P(i:X)(k:ℕ):=if W.top i=k then g i k else f i k
 have hp:W.Fade P:=by
    let t(i:X)(k:ℕ):=if W.top i=k then g i k else 0
    have ht:W.Fade t:=by
       apply Rate.Stair.Fade.of_top ((show W.Poly g from hV).mono (by intro i x hi; split <;> simp;all_goals exact Rate.Stair.Poly.nonneg hV hi)) (fun i x hi hx=>if_neg (Nat.ne_of_gt hx))
    refine (ht.add (show W.Fade f from hU)).mono fun i x hi=> ?_;dsimp only [t,P];split
    next=> exact ⟨Rate.Stair.Poly.nonneg hV hi,le_add_of_nonneg_right (Rate.Stair.Fade.nonneg hU hi)⟩
    next => exact ⟨Rate.Stair.Fade.nonneg hU hi, le_of_eq (zero_add _).symm⟩
 have hq:W.Fade q:= fade_solve (θ:=1/2) (by norm_num) (fun i n h=> (hh ⟨i,n,h⟩).1) hp (fun x i hi=>by
    unfold Stair.stepOnly P; split_ifs with hj hh <;> first | omega | skip
    · exact le_of_eq (tab f g ⟨x,i,hi,hj⟩)
    all_goals have ht:i=W.top x:=by have h:=hi.2;omega
    all_goals first|omega| (rw [ht,zero_add,show q x (W.top x)=_ from tab_top f g x]))
 refine ⟨fun i=>q i.x i.m,hq.mono (fun x k hi=>?_),fun i=>(hh i).2⟩
 rw [wide,dif_pos hi];exact ⟨(hh ⟨x,k,hi⟩).1,le_rfl⟩
end YM.RG08.Mason
