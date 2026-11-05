import YM.TraceExtension.Weir.Nursery
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side} {j:ℕ}
-- Reg Heart money for approximation.Exponential budget exact.
abbrev tileZ(R:Rep G n)(x:ℝ)(i:Tides n G): Support n := brick (tempQ x) (boothC R) i.2
def moneyP (R:Rep G n)(x:ℝ)(Q:Finset (Tides n G))(m:ℕ)(p:Tides n G→ℝ):ℝ:= ∑ i∈Q,|teas i m /peace x| * R.p.mass (tileZ R x i) (p i)
structure Depot (R:Rep G n)(x:ℝ)(P:Vest n)(q m:ℕ) (Y:Gal G n)(F:Peat G n)(A:ℝ):Prop where
    flag (i:Lip n G) : i∈allotZ (Bay n x) m → ∀ j∈ (closeT R x i.1 P q).powerset,Cohort R.p (brick (tempQ x) (boothC R) j) (beaconR i.1) (twigZ R Y F (loc i.2*peace x) i.1 j)
    bill : ∃ s:Tides n G→ℝ,let K:= stemsM R P x m q; moneyP R x K m s ≤ A∧∀ i∈ K,R.p.Regular (tileZ R x i) (radarT R Y F (peace x) i)∧ R.p.supBounds (0:Site n) (tileZ R x i) (radarT R Y F (peace x) i) (s i)
lemma fees_eq {k l:ℕ}(T:Collar G k)(h:k=l):Cube.fee (h ▸ T:Collar G l)=Cube.fee T:=by subst l;rfl
abbrev OrbSize(S:Stage)(G:Gauge)(p:ℕ)(Y T C:ℝ)(x:ℝ):= composeCost S.order (orbAmt Y (thinM x) (shear x) T (sash S x) C (S.order+p+1)) T
lemma pack (G:Gauge)(S:Stage)(m d:ℕ)(T:Collar G S.order)(hm:1≤ m) :∃ C:ℝ,0≤ C ∧∀ᶠ x:ℝ in atTop,∀ (h:ℕ),1100≤h→h≤towerH x d →∀ (n:Side)(Λ:ℝ)(R:Rep G n)(hs:Age S x Λ R) (Y:Gal G n)(F:Peat G n)(L:Vest n),
   Clouded Y (Bay n x)→ Climate Y (S.order+m+1) (thinM x) C → Splendor F (ExtS n x) (S.order+m+1) (shear x) C→ Drift _ F→20*(high x+10)<n.val→ Depot R x L h m Y F (swole x):=by
   obtain ⟨C,K,D,hC,hK,hD,H⟩:= priceT G (Cube.fee T) (Cube.fee_one ..) S.order m hm
   obtain ⟨Z,A,u,hZ,hA,hP⟩:=zested G _ S.power T (Nat.le_trans (by norm_num) S.order_ge); obtain ⟨V,hV,ht⟩:= cast_shape G S m d T
   let p:=S.order; let c:=Cube.fee T; have hp:1≤ c:=Cube.fee_one T
   let S':= OrbSize S G m K c D
   refine ⟨C,hC,?_⟩
   filter_upwards [ht,pulseB S m hm c hp, zealH S G A Z d u hA hZ, minister G S m K c D hm (by positivity) hp hD,eventually_gt_atTop (1:ℝ),(orb_charge S m c K D hp hD (by positivity) hm) 1 (by norm_num)] with x he hE hz hw h hx k hk' hk n Λ R hS Y F L hY hL hU hI hn
   obtain ⟨hf,hp',h',hb,hv,hN,Hh⟩:= he k hk' hk Λ n R hS; obtain ⟨h1,h2,h3⟩:=hz Λ k hk n R hS
   let s:=sash S x; let u':= peace x; obtain ⟨hs₀,hu',h''⟩:= pet x h.le S
   have hTin:0 ≤ thinM x:=(Zn.wake ..).le; have hT':0 ≤ Swift.shear x:=by unfold Swift.shear; positivity[hTin,show 0 < wideM x from Zn.wake ..]
   let T':Collar G R.p.order:=hS.rank.symm ▸ T; have hT:Cube.fee T'=Cube.fee T:= fees_eq ..; let Sg:ℝ:= baubleZ m S K c D G x; have hT'' : 0≤ polar R.p (dreamZ x):=by unfold polar dreamZ; positivity [zenV R.p.order]
   let U:=allotZ (G:=G) (Bay n x) m
   let K'(i:Lip n G):=closeT R x i.1 L k; let X(i:Lip n G)(v:Vest n):= twigZ R Y F (loc i.2*u') i.1 v; let Y' := hY.wider (dec_b ..|>.1);
   have hm(i:Lip n G)(hi:i∈U):∃ f:Vest n→ℝ,(∀ j∈(K' i).powerset,Cohort R.p (brick (tempQ x) (boothC R) j) (beaconR i.1) (X i j) ∧ R.p.Regular (tileZ R x (i,j)) (radarT R Y F u' (i,j))∧ R.p.supBounds (0:Site n) (tileZ R x (i,j)) (radarT R Y F u' (i,j)) (f j))∧
       ∑ j∈ (K' i).powerset.erase ∅, R.p.mass (tileZ R x (i,j)) (f j) ≤ Sg:=by
       let e:=beaconR i.1; let v:=loc i.2*u'; let r:=Cleft x k; let Q:=tempQ x (n:=n); obtain ⟨hx',hj⟩:=mem_product.mp hi; have ho:e.1∈ Bay n x:= (mem_product.mp hx').1; have hQ : Q⊆tower r:=hf.tree; have hO:e.1∈Q:=((dec_b ..).2 ((dec_b ..).1 ho)); have hF:= flair R L k (rim x) e
       obtain ⟨f,hf',hA⟩:= hP (rim x) r k v (V* u') S.width (hue x) 0 (smoke x) S.paths Λ n R (K' i) e Q hS.rank hb hS.paid hS.good hS.coverage hf.paid hp' (h' _ hj) (by omega) (Hh _ ho) (by rw [separation_comm]; simpa[tower, halo_spec] using (hQ hO)) hF (hf.array i hi) (by rw[←hS.paid]; exact hN)
       let C':=rasp e Y F v; have hR : Career R.p Q C' (OrbSize S G m K c D x):=by
           have hR:= H n R.p T' (high x) i.2 Q s u' (Swift.shear x) (thinM x) e Y F hS.rank.symm hT.symm hT' hTin (shifts x S Λ R hS) hv hu' hE.1 hE.2 (fun i hi=>hi) Y' hU hI hL (by omega) (mem_range.mp hj); exact hR
       have hR' : Cohort R.p Q e C':= ((raspT v Y' hI hU.symm hU.locale).up (dec_b .. |>.2))
       obtain ⟨hM,hG⟩:= returns (dreamZ x) 0 (zest R e v) i.1 (boothC R) (K' i) (S' x) h2 h3 hx.1 f hO (fun j hj=>⟨(hf' _ hj).1,hF _ hj|>.1,(hf' _ hj).2⟩) hR' hR (hA.trans h1)
       refine ⟨_,hM,hG.trans ?_⟩
       unfold Sg baubleZ; refine mul_le_mul ?_ ?_ (mul_nonneg (Real.exp_pos _).le hx.1) ?_
       · unfold polar; rw[hS.rank]
       · unfold BudgetPoint.mass; rw [hS.depth]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (tote S x Λ R hS)) S.price_pos.le)) hx.1
       rw [← hS.rank]; exact mul_nonneg zero_le_two hT''
   choose! f hf hK using hm; refine ⟨fun i hi j hj=>(hf i hi j hj).1,fun p=>f p.1 p.2,?_,?_⟩; rotate_left
   · intro i hi; exact (hf i.1 (sting ..|>.mp hi|>.1) i.2 (mem_of_mem_erase (sting ..|>.mp hi|>.2))).2
   have hh : 0 ≤ Sg:=by unfold Sg baubleZ; exact mul_nonneg (mul_nonneg zero_le_two (by unfold dreamZ; positivity [zenV S.order])) (mul_nonneg (Real.exp_pos _).le hx.1)
   unfold moneyP; rw [partedP]; apply le_trans _ hw
   let V:=Sg/u'; let W(i:Lip n G):= |wage m i.2/u'|
   apply le_trans (sum_le_sum (s:=U) (g:=fun i=> W i*Sg) (fun i hi=>?_)); swap
   · have hδ : 0 ≤ W i:= abs_nonneg _; refine le_trans ?_ (mul_le_mul_of_nonneg_left (hK i hi) hδ); rw[Finset.mul_sum]
   unfold U allotZ; rw[sum_product]; let xP:= Bay n x; let X':= Loc G 1
   have hz(i:Lines G n 1) : ∑ j∈range m,W (i,j)*Sg=wheat m*Sg/u':=by unfold W wheat; simp_rw [abs_div,abs_of_pos (show 0 < u' from hu')]; rw[Finset.sum_mul,Finset.sum_div]; exact sum_congr rfl fun _ _=> by ring
   simp_rw [hz,sum_const,nsmul_eq_mul]; rw[mul_div_assoc];
   have hX : 0≤wheat m:=sum_nonneg fun i _=>abs_nonneg _
   refine le_trans (b:=cardB G x*(wheat m*(Sg/u'))) (mul_le_mul_of_nonneg_right ?_ (show 0≤wheat m* (Sg/u') by positivity)) (le_of_eq ?_); rotate_left
   · unfold Sg u'; ring
   rw [card_product]; apply Nat.cast_le.mpr; rw [card_univ]; apply Nat.mul_le_mul_right; exact le_trans (Corona.halo_size ..) (by simp)
end YM.Trace.Weir
