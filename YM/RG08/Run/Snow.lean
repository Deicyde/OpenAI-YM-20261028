import YM.RG08.Run.Work
/-!
# Local invariants for transmitting inserted/stable kernels. Only compact
address; Poll approved. K-graph packets from formal insertions without masks.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type}{u:I→Windows}{w:J→ ShoreP u} {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
local notation "Ⓨ" => wallY X
local notation "Δ" => tiltP X
local notation "Υ" => Ye X ν D' T
local notation "Γ" => heights X ν D'
variable {L:Wall w 1→Wings u 1}{U:Wall w 1→BoardU D R G}{A:Wall w 0→ BoardU D R G}{p : J→ℝ}

-- unified proof pays ONE history's sigma only. Poll t threshold from enabled.
structure Tribe (T:Aperture G P k E τ d D R)(H:Hol G)(F:Labels.Frame G d)(p:J→ℝ)(A:Wall w 0→ BoardU D R G)(U:Wall w 1→BoardU D R G) (e r:ℕ) :Prop where
  cards:Card k (wallY X) (strideP X w p) (fun i=>A i e r) 1
  univ:Card k (wallY X) (strideP X w p) (fun i=>U i e r) 1
  key j : slot (F:=F) j=r → Dig (wallY X) (strideP X w p) (fun i=> coeff e (call H F (U i) j))
lemma season (he: Tights T S ν D' u)(hz: Heirs T' u)(hm:t≤τ)(hk:e ≤ E)(hr:r≤ t+e)(hx: ∀ i, (L i).toLaunch=i.world.toLaunch)(hp:0≤p)
    (hA:∀ i,Crop t (A i) H F)(hP:∀ i,Marvel t (U i))(hU:∀ i,Lank (U i))
    (hT:Card k (fun i=>Ⓨ (Wall.tip w i)) p (fun i=> A (Wall.tip w i) e r) 1)
    (hL:∀ j k,awaits 1 e r j k→ Tribe T' H F p A U j k)
    (hF:Card k Ⓨ (strideP X w p) (fun i=>U i e r- aboard d (babyQ G X (L i)) (A i.roof e r)) 1)
    (hq:(∀ k v:ℕ, v=r→ k=e → ∀ b:Letter F,slot b=v → Dig Ⓨ (strideP X w p) (fun i=>coeff k (call H F (U i) b))) → Card k Ⓨ (strideP X w p) (fun i:Wall w 1=> A i.low e r-U i e r) 1)
    (h : Card k Ⓨ (strideP X w p) (fun i=> A i e r) 1→Card k Ⓨ (strideP X w p) (fun i=> U i e r) 1) : Tribe T' H F p A U e r := by -- simplify binds
   let F' i:= aboard d (babyQ G X (L i)) (A i.roof e r)
   have hE(j:Letter F)(r:ℕ)(hx:r≤τ+E): d*slot j*r ≤ k:= Nat.le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (slot_le _)) hx) T'.budget -- x not present
   have hy(j:Letter F)(hj:slot j=r): Dig Ⓨ (strideP X w p) (fun i=> coeff e (call H F (U i) j)):= by
     simp_rw [call,coeff_mk,auditT]; rw [hj]; refine Dig.sums _ (Wall.plusOne X) (fun n hn=>?_)
     split_ifs with h; swap; exact Dig.zero
     by_cases hn':n=r
     · subst n; rw [Nat.add_sub_cancel]; rw [show (fun i=> invest H (U i e r) j)=(fun i=>invest H (U i e r-F' i) j) from funext fun i=>?_]; · exact cardDig H j hF (hE j _ (by omega))
       obtain ⟨hx,hg,hz⟩:=pollen (e:=e) (L i) (hA i.roof).hU (hA i.roof).paid (hA i.roof).spine he.he j hj
       rw [invest_less H j (seat_made (hP i)) hx (hU _ _ _) hg, show invest H (F' i) j=0 from hz,sub_zero]
     have hx : n < r:= lt_of_le_of_ne (mem_range_succ_iff.mp hn) hn'; exact cardDig H _ ((hL _ _ (Or.inl (by omega:e+n-r<e))).univ) (hE j _ (by omega:n≤τ+E)) -- hE specific r
   have hk': Card k Ⓨ (strideP X w p) (fun i=> A i e r) 1 := by
     apply traverse (P:=fun i=>A i e r) (Q:=F') hp (show (0:Wall w 0→ℝ) ≤ 1 from zero_le_one) hT
     · intro i C hp
       have hi : gain X.S (1/2) (L i).i ((L i).i+1)=gain X.S (1/2) i.i (i.i+1):= by rw [show (L i).i=i.i from congr_arg Launch.i (hx i)]
       rw [← hi]; exact Heirs.contract hz (L i) _ ((hA i.roof).paid e r) (held H (hA i.roof).hU (hA i.roof).paid (hA i.roof).spine e r) (by omega) _ hp
     rw [show (fun i=> A i.low e r- F' i)=(fun i=> A i.low e r-U i e r)+(fun i:Wall w 1=> U i e r-F' i) from funext fun i=>(sub_add_sub_cancel ..).symm]
     exact (hq (fun _ _ hA H=> H.symm ▸ hA.symm ▸ hy)).more hF zero_le_one (Wall.plusOne X)
   exact ⟨hk',h hk',hy⟩
lemma planned (hm:t≤τ)(hp:r>t+e)(hA:∀ i,Marvel t (A i))(hP:∀ i,Marvel t (U i)) : Tribe T' H F p A U e r:= by -- indices
    constructor
    · simp_rw [show ∀ i,A i e r=0 from fun i=> not_ne_iff.mp (mt ((hA i).cap e r) (by omega))]; exact Card.zero
    · simp_rw [show ∀ i,U i e r=0 from fun i=> not_ne_iff.mp (mt ((hP i).cap e r) (by omega))]; exact Card.zero
    intro j hj; simp_rw [call, coeff_mk,fun i=>audit_cap H (hP i).cap j (e:=e) (by omega)]; exact Dig.zero
end YM.RG08.Run
