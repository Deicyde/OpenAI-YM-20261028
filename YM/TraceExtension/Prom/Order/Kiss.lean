import YM.MergeProof.West.Kilo
import YM.TraceExtension.Prom.Order.Launch
import YM.TraceExtension.Prom.Front.West.Eark
import YM.TraceExtension.Prom.Port.Soft.Royal
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Function Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Display Display.Docking Filter RG.Supply Next.Rank.Station Finset Bid West
open scoped Topology BigOperators Classical
variable {G : Gauge}
def strideX (K:KernelChoices)(P:Purse)(u j:ℕ)(L:Side):Prop:= ∀ n:ℕ, n ≤ u → Radian.Weight L.val (trainSky K j) P.band (Glimmer.fuel P.taylor n/4)

/-- one tax table. EMPLOY either J or J-1 during stop range. Buy at the SMALLER coarser factor too. -/
def Crossings (j : ℕ) (X:Sheet G)(B:MapPrices)(P:Purse)(L:Side):Prop:= ∀ k∈ ({j,j-1}:Finset ℕ),∀ i∈ ({j,j-1}:Finset ℕ), i ≤ k → BrevitySky (G:=G) B X.kernel k i P L ∧ ∀ y:ℝ,0≤ y→ Soft.AvailableSky (G:=G) (initials B X.profile X.kernel k i) L P y
structure Roh (X:Sheet G)(B:MapPrices)(j:ℕ)(P:Purse)(u:ℕ)(L:Side):Prop where
   reg (k:ℕ)(hk:k∈({j,j-1}:Finset ℕ)) : Regiment P (X.profile k) L ∧ Steel P (X.profile k) L
   coast : HLane P u L
   commission : strideX X.kernel P u j L
   merit : Crossings j X B P L
structure RouteSky {ι:Type} (X:Sheet G)(B:MapPrices)(u:ℕ)(d:ℕ)(P:ι→Tapes.Panel d):Prop where
    Coulomb i j : Coul ((P i).bag j) u
    pin i j : ((P i).θ=(P j).θ) ∧ ∀ n:ℕ, ((P i).bag n).era.coast.Q=((P j).bag n).era.coast.Q
    estate (j:ℕ)(i:ι) (h:(P i).θ+1 ≤ (X.profile (j-1)).order): ∃ m:ℕ,∀ L : Side,m ≤ L.val → Roh X B j ((P i).bag j) u L
private lemma x_pulseSky {p : Purse} {A : Stage} (h:p.budget) (he:stipend A p) (hp:p.goal+4 ≤ p.taylor) (hx:0≤p.band)
    (ht:p.horizon+10 ≤ p.era.coast.Q) (hz:10 ≤ p.horizon) :
    ∃ k : ℕ, ∀ v : Side,k≤v.val → Regiment p A v := by
  obtain ⟨k,H⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (pulse_ok p hx))
  exact ⟨k+128*p.era.coast.Q,fun v hV=> ⟨h,H v (by omega),he,hp,ht,hz,by omega⟩⟩
variable {ι:Type} [Finite ι]
private def tabsSky (X:Sheet G)(B:MapPrices)(j:ℕ) :=
 let V:= ({j,j-1}:Finset ℕ); ∑ i∈V, ∑ v∈V, |capitalSky X.kernel B i v|
private lemma c_rink (X:Sheet G)(B:MapPrices)(j i l:ℕ)(hi:i∈({j,j-1}:Finset ℕ))(hl:l∈({j,j-1}:Finset ℕ)): capitalSky X.kernel B i l ≤ tabsSky X B j := by
    apply (le_abs_self _).trans
    exact (single_le_sum (fun _ _=> abs_nonneg _) hl).trans (single_le_sum (fun i _=> sum_nonneg (f:=fun l=> |capitalSky X.kernel B i l|) fun j _=> abs_nonneg _) hi)
lemma y_purchasesSky (X:Sheet G)(B:MapPrices)(z:ι→ℝ)(u d:ℕ)(hu:2 ≤ u)(hb:∀ i,d+6≤ z i) : ∃ P:ι→Tapes.Panel d,(∀ i,(P i).arc=z i) ∧ RouteSky X B u d P:=by
   have hZ: BddAbove (Set.range z):= (Set.finite_range z).bddAbove
   obtain ⟨Z,hZ⟩:=hZ
   let c:=max Z 0; have hx:0≤ c:=le_max_right ..; have he (i):0≤ z i:= by linarith only [hb i, Nat.cast_nonneg (α:=ℝ) d]
   let credit:ℝ:= c*d+d+2; have hc : 1 ≤ credit:=by unfold credit; have hp:0 ≤ c*d:=mul_nonneg hx (Nat.cast_nonneg _); linarith only [hp, Nat.cast_nonneg (α:=ℝ) d]
   obtain ⟨T,hT,ht⟩:= ((pays_p credit u).and (eventually_le_atBot (-8-credit))).exists
   let U:ℝ:=1/16-T; have hε:0 ≤ U:=by unfold U; linarith only [ht,hc]
   obtain ⟨n,hn⟩:= exists_nat_ge ((u:ℝ)*U+10); let i:= n+d+5; have hP:2*U ≤ u*U:=by exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hε
   have hn':(6:ℝ) ≤ n:= by linarith only [hP,hn,hε]
   obtain ⟨Φ,hφ,hg⟩:= ((earns_p credit n i u).and (eventually_ge_atTop (n+10*(2*credit+3+8*i+10)+10))).exists
   choose S0 hS using entries X B
   let Arc j:= (X.profile (j-1)).clip.linear/20
   let S j := { S0 j with kernel:=max 1 (tabsSky X B j)
                          awake:= le_max_left ..
                          ζ:= min (S0 j).ζ (Arc j)
                          pulse:= lt_min (S0 j).pulse (div_pos (X.profile (j-1)).clip.tail_pos (by norm_num))
                          warm:= (min_le_left ..).trans (S0 j).warm }

   let M:ℕ:= (6*u+3)*(3+2*u)+30
   let Q:=M+10
   let J:= fun x=> (⟨Q,(S x).trunk,(X.profile x).price_pos.le.trans (S x).road,U,U,hε,hε,(S x).ζ,(S x).pulse⟩ : Demand)
   let g:=fun x=>(⟨J x,(S x).shape,(S x).ceiling⟩:Era)
   let p':= fun (y:ι) x=> (⟨g x,i,n,M,z y,credit,T,Φ,(S x).kernel,by linarith only [hg,hc,hn',Nat.cast_nonneg (α:=ℝ) i],
                        (S x).awake,hc,by linarith only [ht],(J x).base, by exact_mod_cast hn',by change _*U+_≤_; linarith only [hn,hP],by change 1/16-U=T; unfold U;ring,rfl⟩ : Purse)
   let A:ι→Tapes.Panel d:= fun χ=>⟨p' χ,z χ,hb χ,T,i,by unfold i;omega,fun _=>rfl,fun _=>rfl,fun _=> add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_right (le_trans (hZ (Set.mem_range_self χ)) (le_max_left Z 0)) (Nat.cast_nonneg _)) _) _,fun _=>rfl⟩
   refine ⟨A,fun _=>rfl,fun χ j=>⟨?_, ?_,hT,hφ⟩,fun _ _ =>⟨rfl,fun _=>rfl⟩,fun j χ hj=> ?_⟩
   · intro n hn; change _ ≤ M/_; apply (Nat.le_div_iff_mul_le (by omega : 0<3+2*n)).2; exact le_trans (Nat.mul_le_mul (show 6*n+3≤6*u+3 by omega) (show 3+2*n≤3+2*u by omega)) (by unfold M; omega)
   · change 1- (n:ℝ) ≤ -(↑u * U)-2; linarith only [hn]
   let P:=p' χ j; let a:= credit; let b:= X.profile j
   let U:= ({j,j-1}:Finset ℕ)
   have heC (k)(hk:k ∈ U): stipend (X.profile k) P:= by
     have hh:k=j ∨ k=j-1:= by simpa only [U, Finset.mem_insert, mem_singleton] using hk
     have hY := X.prices (show k ≤ j by omega)
     refine ⟨(hY.trans ((S j).road)).trans (by change _≤(S j).trunk+2;linarith only),?_,hj.trans (X.orders (show j-1 ≤ k by omega))⟩
     rcases hh with h|h; rw [h]; exact (S j).warm; rw [h]; exact min_le_right ..
   have hU1 (k)(hk:k∈U) :∃ t:ℕ,∀ L:Side,t ≤ L.val → Regiment P (X.profile k) L ∧ Steel P (X.profile k) L:=by
      obtain ⟨t,ht⟩:= x_pulseSky (p:=P) hg (heC _ hk) (show n+4 ≤ i by unfold i; omega) (he χ) (le_refl _) (show 10≤M by unfold M;omega)
      let r:=(X.profile k).supportExponent; have hx:0 < r:= (X.profile k).price_pos
      obtain ⟨ζ,hζ⟩:= exists_nat_ge (10*(15:ℝ)^4 * Docking.increment (load P.era+1)/r)
      exact ⟨t+ζ,fun L H=> ⟨ht L (by omega),(div_le_iff₀ hx).mp (hζ.trans (Nat.cast_le.mpr (show ζ ≤ _ by omega))), (heC k hk).1⟩⟩
   choose! t ht using hU1
   obtain ⟨t₁,hL⟩:= lsizing P u
   obtain ⟨t₂,hQ⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ((eventually_all_finset (Finset.range (u+1))).2 (fun n _=> Radian.enough_room (n:=P.taylor) (m:=n) _ (trainSky_at X.kernel j) (he χ))))
   have hr : 0 < (S j).trunk := (X.profile j).price_pos.trans_le (S j).road
   obtain ⟨l,hU⟩:= fragrant hr; obtain ⟨y,hW⟩:= fragrant (show 0<(S j).trunk+2 by linarith only [hr]); obtain ⟨h1,h2,h3⟩:= hS j
   have hk (i v) (hi:i∈U)(hv:v∈U)(h:v ≤ i) : ∃ t:ℕ,∀ L:Side, t ≤ L.val → BrevitySky (G:=G) B X.kernel i v P L ∧ ∀ y:ℝ,0≤ y→ Soft.AvailableSky (G:=G) (initials B X.profile X.kernel i v) L P y:=by
      obtain ⟨t₃,ht₃⟩:= sizing_gap (max (B.Ω i) (B.Ω v)) G
      obtain ⟨r,hr⟩:= Soft.solubleSky (G:=G) (initials B X.profile X.kernel i v) P
      refine ⟨l+y+t₃+r,fun L hV=>⟨?_, hr L (by omega)⟩⟩
      exact ⟨(c_rink X B j i v hi hv).trans (le_max_right ..), (show 30 ≤ M by unfold M;omega), ht₃ L (by omega),⟨h3.1,h3.2⟩, hW L (by omega),hU L (by omega)⟩
   choose! q hq using hk
   let w₁:= U.sup t;let w₂:= U.sup (fun i=>U.sup (q i))
   refine ⟨t₁+t₂+w₁+w₂,fun L hV=> ⟨fun i hi=> ht _ hi _ ((le_sup (f:=t) hi).trans (show w₁ ≤ _ by omega)),hL L (by omega), fun n hn=> hQ L.val (by omega) n (mem_range.mpr (by omega)), fun k hk v hv hv'=> ?_⟩⟩
   apply hq k v hk hv hv'; exact ((le_sup (f:=q k) hv).trans (le_sup (f:=fun i=>U.sup (q i)) hk)).trans (show w₂ ≤ _ by omega)
end YM.PhysicalNext.InteractingRank
