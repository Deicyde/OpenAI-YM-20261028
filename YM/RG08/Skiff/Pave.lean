import YM.RG08.Skiff.Pocket
import YM.RG08.Forms.Pontoon

/-! # Marked row replacement

**Whole** weighted row test (arbitrary outputs; includes post and pre-block
Newton cases). No summation is defaulted, including arity zero. Changing test
jets may depend on both positions (must be bounded in the transformed
norm). TsuM over both entire palettes. Appropriately pay the exponential
warp shrinking or cancellation explicitly in Source consumers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Forms Pert.Bulk Jetty Function Finset
open scoped BigOperators Topology ENNReal ContDiff Classical
variable {I J:Type}{L:Loom I}{G:Loom J}{n m d e:ℕ}{σ τ B C D:ℝ}{h:0<σ}{k:0<τ}

abbrev Words:=Pearl→Pearl
structure Say (W:Words):Prop where
 add : ∀ p q:Pearl,W (p+q)=W p+W q
 smul : ∀ (a:ℝ)(p:Pearl),W (a • p)=a • W p
lemma Say.song {W:Words}{F:NoteX}(hv:Say W)(hp:Voice F): Voice (F ∘ W):=⟨fun x y=>by simp only [Function.comp_apply,hv.add,hp.plus],fun a x=>by simp only [Function.comp_apply,hv.smul,hp.hum]⟩
lemma shares{W:Words}{F:NoteX}(hs:Voice F)(hw:∀ p,beam e k p≤1 → beam d h (W p) ≤ B) : purse e k (F ∘ W) ≤ purse d h F * ENNReal.ofReal B:=by
 refine purse_le _ _ fun f hf=> (purse_gives _ _ hs (W f)).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hw f hf)) _)

abbrev Dance (n m:ℕ)(I J:Type):=Tape n I→Tape m J→ℝ
abbrev Lib (n m:ℕ)(I J:Type):=Tape n I→Tape m J→Words
variable {A:Dance n m I J}{W:Lib n m I J}{F:Pack n I}
def act (l:Loom J)(_e:ℕ)(_k:0<τ)(A:Dance n m I J)(M:Dance n m I J)(x:Tape n I)(y:Tape m J):=ENNReal.ofReal |A x y| * ENNReal.ofReal (M x y)*weft l τ y
-- free e & k implicit unused, track in structure
structure Play (L:Loom I)(G:Loom J)(d e:ℕ)(h:0<σ)(k:0<τ)(A:Dance n m I J)(W:Lib n m I J)(C:ℝ):Prop where
 gain : 0≤C
 telled : ∀ x y,Say (W x y)
 record : ∃ M:Dance n m I J,(∀ x y,0≤M x y) ∧ (∀ x y, A x y≠0→∀ p,beam e k p≤1 → beam d h (W x y p)≤M x y) ∧
    ∀ x,(∑' y,act G e k A M x y) ≤ ENNReal.ofReal C * weft L σ x

def reel (A:Dance n m I J)(W:Lib n m I J)(F:Pack n I):Blue m J (Tape n I):=fun y x=> A x y • (F x ∘ W x y)
lemma reeling (he:Lyrics F)(hP:Play L G d e h k A W C):Bare (reel A W F):=fun y x=> ((hP.telled x y).song (he x)).smul _
lemma paid (he:Lyrics F)(hf:Sings L d h F B)(hP:Play L G d e h k A W C):CableCar G e k (reel A W F) (ENNReal.ofReal (B*C)):=by
 obtain ⟨hc,hx,M,hM,hm,ha⟩:=hP -- use rcases ? '-' kills? bug; edit
 have ht (x:Tape n I)(y:Tape m J): fruit G e k (reel A W F) y x ≤ act G e k A M x y * purse d h (F x):=by
    unfold fruit reel act
    by_cases hz:A x y=0
    · simp [hz,purse_zero]
    apply (mul_le_mul_left ((purse_smul ..).trans (mul_le_mul_right (shares (he x) (hm x y hz)) _)) _).trans_eq
    ac_rfl
 unfold CableCar; rw [ENNReal.tsum_comm]
 apply (ENNReal.tsum_le_tsum fun x=> ENNReal.tsum_le_tsum fun y=> ht x y).trans
 simp_rw [ENNReal.tsum_mul_right]
 refine (ENNReal.tsum_le_tsum (g:=fun x:Tape n I=> ENNReal.ofReal C * gems L d h F x) (fun x=>(mul_le_mul_left (ha x) _).trans_eq ?_)).trans ?_
 · unfold gems; ac_rfl
 rw [ENNReal.tsum_mul_left,mul_comm B C,ENNReal.ofReal_mul hc];exact mul_le_mul_right hf _

def picture (A:Dance n m I J)(W:Lib n m I J)(F:Pack n I):Pack m J:=decker (reel A W F)
lemma playing (he:Lyrics F)(hf:Sings L d h F B)(hP:Play L G d e h k A W C):Lyrics (picture A W F) ∧ Sings G e k (picture A W F) (B*C):=by
 have hv:=paid he hf hP;exact ⟨hv.lyric (reeling he hP), hv.sings⟩
lemma showtime (he:Lyrics F)(hf:Sings L d h F B)(hP:Play L G d e h k A W C)(y:Tape m J)(f:Pearl):Summable (fun x:Tape n I=>‖A x y * F x (W x y f)‖):=(paid he hf hP).deep (reeling he hP) y f

/-- Reindexing or other per-leg pullback with no address move, monotone decreasing
formal widths. EXPONENTIAL for repeated quantitative application. Include charge even on first and last, even scalar. -/
def audio (n m:ℕ)(I J:Type):Lib n m I J:=fun _ _ f=>f
def candles (K:Cables n I J):Dance n n I J:=design K
variable {E K:Cables n I J}{p:Fin n→ℝ}
structure Parade (L:Loom I)(G:Loom J)(σ:ℝ)(E K:Cables n I J)(p:Fin n→ℝ):Prop where
 beamE : ∀ i x y,K i x y≠0 → σ*G.height y≤σ*L.height x+E i x y
 bulbs : ∀ i x y,0≤E i x y
 amount : ∀ i,0≤p i
 leaves : ∀ i x,(∑' y,bill (K i x y) (E i x y))≤ENNReal.ofReal (p i)
lemma Parade.vert (pv:Parade L G σ E K p)(x:Tape n I)(y:Tape n J)(hx:design K x y≠0)(h:0<σ):
 σ* G.cage y ≤ σ * L.cage x + ∑ i,E i (x i) (y i):=by
 rw [mul_comm,← le_div_iff₀ h]
 have hg:0≤ ∑ i,E i (x i) (y i):=sum_nonneg fun i _=>pv.bulbs i _ _
 refine G.racks _ (div_nonneg (add_nonneg (mul_nonneg h.le (L.cage_nn _)) hg) h.le) fun i=>?_
 rw [le_div_iff₀ h,mul_comm]; refine (pv.beamE _ _ _ (prod_ne_zero_iff.mp hx i (mem_univ _))).trans (add_le_add ?_ (single_le_sum (fun j _=>pv.bulbs j (x j) (y j)) (mem_univ i)))
 exact mul_le_mul_of_nonneg_left (L.float x i) h.le
private lemma forger (s:Finset (Fin n))(hf:∀ i∈s,0≤p i):ENNReal.ofReal (∏ i∈s,p i)=∏ i∈s,ENNReal.ofReal (p i):=by
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert i s hi ih=> rw [prod_insert hi,prod_insert hi,ENNReal.ofReal_mul (hf i (by simp)), ih (fun i hi=>hf i (by simp [hi]))]
lemma Parade.play (pv:Parade L G σ E K p)(hs:τ≤σ)(hu:d≤e):Play L G d e h k (candles K) (audio n n I J) (∏ i,p i):=by
 refine ⟨prod_nonneg (fun i _=>pv.amount _),fun x y=>⟨by intros;rfl,by intros;rfl⟩,fun _ _=>1, by simp,fun x y _ f hf=>(beam_smaller h k hs hu f).trans hf,fun x=>?_⟩
 let U(x:Tape n I)(y:Tape n J):=∏ i,cable E K i (x i) (y i)
 have ht(y:Tape n J): act G e k (candles K) (fun _ _=>1) x y ≤ U x y * weft L σ x:=by
   unfold act candles weft
   rw [ENNReal.ofReal_one,mul_one]
   by_cases hz:design K x y=0
   · simp [hz]
   let z:=∑ i,E i (x i) (y i)
   have hf:τ*G.cage y ≤ z+σ*L.cage x:= (mul_le_mul_of_nonneg_right hs (G.cage_nn y)).trans ((pv.vert x y hz h).trans_eq (add_comm ..))
   apply (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hf)) _).trans_eq
   unfold U z; rw [stamp,show bill (design K x y) (∑ i,E i (x i) (y i))=_ from bill_products (fun i=>K i (x i) (y i)) (fun i=>E i (x i) (y i))]
   rfl
 apply (ENNReal.tsum_le_tsum ht).trans
 rw [ENNReal.tsum_mul_right];apply mul_le_mul_left ?_ (weft L σ x)
 unfold U cable; rw [all_Δ (a:=fun i (j:J)=> bill (K i (x i) j) (E i (x i) j)),forger _ fun i _=>pv.amount i];exact prod_le_prod' fun i _=>pv.leaves i (x i)
end YM.RG08.Skiff
