import YM.MergeProof.West.Bera
import YM.MergeProof.West.Eark
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Timers


set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Function Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Display Display.Docking Filter RG.Supply Next.Rank.Station Finset Bid West
open scoped Topology BigOperators Classical
variable {G : Gauge}
structure Route {ι:Type} (X:Sheet G)(B:MapPrices)(u:ℕ)(d:ℕ)(P:ι→Tapes.Panel d):Prop where
    Coulomb i j : Coul ((P i).bag j) u
    pin i j : ((P i).θ=(P j).θ) ∧ ∀ n:ℕ, ((P i).bag n).era.coast.Q=((P j).bag n).era.coast.Q
    estate (j : ℕ)(i : ι) (h:(P i).θ+1 ≤ (X.profile j).order):∃ m:ℕ,∀ (L:Side),m ≤ L.val → Regiment ((P i).bag j) (X.profile j) L ∧ HLane ((P i).bag j) u L ∧ reserve (prepared X.kernel) j (P i).θ (P i).arc L.val ∧ reserveX (prepared X.kernel) u j (P i).θ (P i).arc L.val ∧ Brevity (G:=G) B X.kernel j ((P i).bag j) L ∧ Steel ((P i).bag j) (X.profile j) L
private lemma x_pulse {p : Purse} {A : Stage} (h:p.budget) (he:stipend A p) (hp:p.goal+4 ≤ p.taylor) (hx:0≤p.band)
    (ht:p.horizon+10 ≤ p.era.coast.Q) (hz:10 ≤ p.horizon) :
    ∃ k : ℕ, ∀ v : Side,k≤v.val → Regiment p A v := by
  obtain ⟨k,H⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (pulse_ok p hx))
  exact ⟨k+128*p.era.coast.Q,fun v hV=> ⟨h,H v (by omega),he,hp,ht,hz,by omega⟩⟩
variable {ι:Type} [Finite ι]
lemma y_purchases (X:Sheet G)(B:MapPrices)(z:ι→ℝ)(u d:ℕ)(hu:2 ≤ u)(hb:∀ i,d+6≤ z i) : ∃ P:ι→Tapes.Panel d,(∀ i,(P i).arc=z i) ∧ Route X B u d P:=by
   have hZ: BddAbove (Set.range z):= (Set.finite_range z).bddAbove
   obtain ⟨Z,hZ⟩:=hZ
   let c:=max Z 0; have hx:0≤ c:=le_max_right ..; have he (i):0≤ z i:= by linarith only [hb i, Nat.cast_nonneg (α:=ℝ) d]
   let credit:ℝ:= c*d+d+2; have hc : 1 ≤ credit:=by unfold credit; have hp:0 ≤ c*d:=mul_nonneg hx (Nat.cast_nonneg _); linarith only [hp, Nat.cast_nonneg (α:=ℝ) d]
   obtain ⟨T,hT,ht⟩:= ((pays_p credit u).and (eventually_le_atBot (-8-credit))).exists
   let U:ℝ:=1/16-T; have hε:0 ≤ U:=by unfold U; linarith only [ht,hc]
   obtain ⟨n,hn⟩:= exists_nat_ge ((u:ℝ)*U+10); let i:= n+d+5; have hP:2*U ≤ u*U:=by exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hε
   have hn':(6:ℝ) ≤ n:= by linarith only [hP,hn,hε]
   obtain ⟨Φ,hφ,hg⟩:= ((earns_p credit n i u).and (eventually_ge_atTop (n+10*(2*credit+3+8*i+10)+10))).exists
   choose S hS using entries X B
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
   have ht:stipend b P:= ⟨le_trans (S j).road (by change _≤(S j).trunk+2;linarith only),(S j).warm,hj⟩
   obtain ⟨t,ht⟩:= x_pulse (p:=P) hg ht (show n+4 ≤ i by unfold i; omega) (he χ) (le_refl _) (show 10≤M by unfold M;omega)
   obtain ⟨t₁,hL⟩:= lsizing P u; let F:= prepared X.kernel
   obtain ⟨t₂,hQ⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ((reserving F j i (he χ)).and (reservingX F j i (u:=u) (he χ))))
   obtain ⟨t₃,ht₃⟩:= sizing_gap (B.Ω j) G
   have hr : 0 < (S j).trunk := (X.profile j).price_pos.trans_le (S j).road
   obtain ⟨l,hU⟩:= fragrant hr; obtain ⟨y,hW⟩:= fragrant (show 0<(S j).trunk+2 by linarith only [hr]); obtain ⟨h1,h2,h3⟩:= hS j
   let r:=b.supportExponent; have hx: 0 < r:= b.price_pos
   obtain ⟨ζ,hζ⟩:= exists_nat_ge (10*(15:ℝ)^4 * Docking.increment (load P.era+1)/r)
   refine ⟨t+t₁+t₂+t₃+l+y+ζ,fun L hV=>?_⟩
   have he := ht L (by omega); have hP:=hQ L.val (by omega)
   exact ⟨he,hL L (by omega),hP.1,hP.2,⟨h1,(show 30≤M by unfold M;omega),ht₃ L (by omega),⟨h3.1,h3.2⟩, hW L (by omega),hU L (by omega)⟩,(div_le_iff₀ hx).mp (hζ.trans (Nat.cast_le.mpr (show ζ ≤ L.val by omega))),he.aptitude.1⟩
end YM.PhysicalNext.InteractingRank
