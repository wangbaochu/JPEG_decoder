#include <stdio.h>
#include <malloc.h>
#include <math.h>
#include <stdlib.h>
#define PI 3.1415927
#define widthbytes(i) ((i+31)/32*4)//��ʾBMPͼ��ÿһ�е��ֽ������������ĸ��ֽڵ�Ҫ����
int sampleYH,sampleYV,sampleUH,sampleUV,sampleVH,sampleVV;
int HYtoU,VYtoU,HYtoV,VYtoV,YinMCU,UinMCU,VinMCU;
int compressnum=0;//ͼ������ĸ���
int Qt[3][64];//����DCT������һ�������ֻ��������
int *YQt,*UQt,*VQt;//ָ���ͼ��������õ�������
int codepos[4][16];//����Ϊj�ĵ�һ�������ڵ���(����Ӧ��codevalue��ֵ����ֵ��0��ʼ)
int codelen[4][16];//codelen��ʾÿ�����ȵ����Ӧ�ĸ���
unsigned char YDCindex,YACindex,UVDCindex,UVACindex;
unsigned char compressindex[3];//��ʾ�ڼ���ͼ������ı��
unsigned char HufTabindex;//��ʾ�ڼ���huf��
unsigned char And[9]={0,1,3,7,0xf,0x1f,0x3f,0x7f,0xff};
unsigned int codevalue[4][256];//codevalue[4][j]=(Z,R)���������к�
unsigned int hufmin[4][16];//hufmin[4][j]��ʾj+1���ȵ���Ŀ�ʼ�루������intֵ��ʾ�ģ�
unsigned int hufmax[4][16];//��ʾj���ȵ���Ľ����루������intֵ��ʾ�ģ�                                       
int bitpos=0,curbyte=0,run=0,value=0,MCUbuffer[10*64],blockbuffer[64];
//blockbuffer[64]����һ����
//value��ʾÿ����������ֵ������ǵ�һ�������ʾֱ��������ֺ��ֵ��
//value��DecodeMCUBlock������Ҫ��Ӳ��ܵõ�������ֱ��ϵ��
//run��ʾÿ������ϵ��֮ǰ��0�ĸ���
 int tempp=0; //��ʾ��ȡhuf��ʱ�����ĳ��ȣ������жϱ��Ƿ����
//
int intervalflag=0,interval=0,restart=0;
//restart=Ri��DRI���е���������ֽ�Ri�������ֽڱ�ʾһ��SCAN��ÿ��
//MCU-Segment���������MCU�ĸ���������segment֮����RST��־�֣�RST=0����0��7ѭ����
//interval��ʾÿ��segment��ѭ�����˵ڼ���MCU��interval=0-Ri��
//intervalflag=0��ʾһ��segment��MCUѭ�������������ڶ���segment������ʼ
int ycoef=0,ucoef=0,vcoef=0;//coef��ÿ����ĵ�һ��ϵ������ʾÿ�����ֱ������
long Y[4*64],U[4*64],V[4*64],QtZMCUbuffer[10*64];//QtZMCUbuffer��ʾ�����������MCU������
unsigned long imgwidth=0,imgheight=0,width=0,height=0,linebytes;
int Z[8][8]={{0,1,5,6,14,15,27,28},{2,4,7,13,16,26,29,42},
{3,8,12,17,25,30,41,43},{9,11,18,24,31,40,44,53},
{10,19,23,32,39,45,52,54},{20,22,33,38,46,51,55,60},
{21,34,37,47,50,56,59,61},{35,36,48,49,57,58,62,63}};//zig-zag���е�˳������
struct  
{//BMPλͼ�ļ�ͷ���ܹ�14���ֽ�
//	unsigned short int type;//�����ֽڣ�ָ���ļ����ͣ�������0x424D�����ַ���"BM"
	unsigned long size;//�ĸ��ֽڣ�ָ���ļ���С��������14���ֽڵ��ļ�ͷ��
	unsigned long reserved;//�ĸ��ֽڣ�Ϊ�����֣����ÿ���
	unsigned long offset;//�ĸ��ֽڣ�Ϊ���ļ�ͷ��ʵ�ʵ�λͼ���ݵ�ƫ���ֽ��������ļ�ͷ+��Ϣͷ+��ɫ��
}head;
struct  
{///BMPλͼ��Ϣͷ������ṹ�ĳ����ǹ̶��ģ�Ϊ40���ֽ�(LONGΪ32λ����)
	unsigned long size;//ָ������ṹ�ĳ��ȣ�Ϊ40
	unsigned long width;//ָ��ͼ��Ŀ�ȣ���λ������,ÿһ�е��ֽ���������4��������,������ǣ�����Ҫ���룬���һ��Ҳ������
    unsigned long height;//ָ��ͼ��ĸ߶ȣ���λ������
//  unsigned short int plane;//������1�����ÿ���
//	unsigned short int bitcount;//ָ����ʾ��ɫʱҪ�õ���λ�������õ�ֵΪ1(�ڰ׶�ɫͼ), 4(16ɫͼ), 
            	// 8(256ɫ),24(���ɫͼ)(�µ�.bmp��ʽ֧��32λɫ������Ͳ���������)��
//	unsigned long compression;//ָ��λͼ�Ƿ�ѹ������Ч��ֵΪBI_RGB��BI_RLE8��BI_RLE4��
	//BI_BITFIELDS(����һЩWindows����õĳ���)��Ҫ˵�����ǣ�Windowsλͼ���Բ���RLE4��
	//��RLE8��ѹ����ʽ�����õĲ��ࡣ���ǽ�������۵�ֻ�е�һ�ֲ�ѹ�����������biCompressionΪBI_RGB�����
   
//	unsigned long imagesize;//ָ��ʵ�ʵ�λͼ����ռ�õ��ֽ���.���CompressionΪBI_RGB����������Ϊ��
//	unsigned long xpels;//ָ��Ŀ���豸��ˮƽ�ֱ��ʣ���λ��ÿ�׵����ظ���
//   unsigned long ypels;//ָ��Ŀ���豸�Ĵ�ֱ�ֱ��ʣ���λͬ��
//	unsigned long colorused;//ָ����ͼ��ʵ���õ�����ɫ���������ֵΪ�㣬���õ�����ɫ��Ϊ2^bitCount
//	unsigned long colorimportant;//ָ����ͼ������Ҫ����ɫ���������ֵΪ�㣬����Ϊ���е���ɫ������Ҫ��
}bmp;
struct  
{///BMPλͼ��Ϣͷ������ṹ�ĳ����ǹ̶��ģ�Ϊ40���ֽ�(LONGΪ32λ����)
//	unsigned long size;//ָ������ṹ�ĳ��ȣ�Ϊ40
//	unsigned long width;//ָ��ͼ��Ŀ�ȣ���λ������,ÿһ�е��ֽ���������4��������,������ǣ�����Ҫ���룬���һ��Ҳ������
//  unsigned long height;//ָ��ͼ��ĸ߶ȣ���λ������
//  unsigned short int plane;//������1�����ÿ���
//	unsigned short int bitcount;//ָ����ʾ��ɫʱҪ�õ���λ�������õ�ֵΪ1(�ڰ׶�ɫͼ), 4(16ɫͼ), 
            	// 8(256ɫ),24(���ɫͼ)(�µ�.bmp��ʽ֧��32λɫ������Ͳ���������)��
	unsigned long compression;//ָ��λͼ�Ƿ�ѹ������Ч��ֵΪBI_RGB��BI_RLE8��BI_RLE4��
	//BI_BITFIELDS(����һЩWindows����õĳ���)��Ҫ˵�����ǣ�Windowsλͼ���Բ���RLE4��
	//��RLE8��ѹ����ʽ�����õĲ��ࡣ���ǽ�������۵�ֻ�е�һ�ֲ�ѹ�����������biCompressionΪBI_RGB�����
   
	unsigned long imagesize;//ָ��ʵ�ʵ�λͼ����ռ�õ��ֽ���.���CompressionΪBI_RGB����������Ϊ��
	unsigned long xpels;//ָ��Ŀ���豸��ˮƽ�ֱ��ʣ���λ��ÿ�׵����ظ���
    unsigned long ypels;//ָ��Ŀ���豸�Ĵ�ֱ�ֱ��ʣ���λͬ��
	unsigned long colorused;//ָ����ͼ��ʵ���õ�����ɫ���������ֵΪ�㣬���õ�����ɫ��Ϊ2^bitCount
	unsigned long colorimportant;//ָ����ͼ������Ҫ����ɫ���������ֵΪ�㣬����Ϊ���е���ɫ������Ҫ��
}bmp2;

/*******************************************************************************************
һ����˵��.bMP�ļ������ݴ��µ��ϣ������ҵġ�Ҳ����˵�����ļ������ȶ�������ͼ��������һ�е�
��ߵ�һ�����أ�Ȼ������ߵڶ������ء����������ǵ����ڶ�����ߵ�һ�����أ���ߵڶ������ء���
�������� �����õ�����������һ�е�����һ�����ء�

�����õ���ɫ���λͼ��ͼ�����ݾ��Ǹ��������ڵ�ɫ���е�����ֵ���������ɫͼ��ͼ�����ݾ���ʵ�ʵ�R��G��Bֵ��
�������2ɫ��16ɫ��256ɫλͼ�����ɫλͼ�ֱ���ܡ�
����2ɫλͼ����1λ�Ϳ��Ա�ʾ�����ص���ɫ(һ��0��ʾ�ڣ�1��ʾ��)������һ���ֽڿ��Ա�ʾ8�����ء�
����16ɫλͼ����4λ���Ա�ʾһ�����ص���ɫ������һ���ֽڿ��Ա�ʾ2�����ء�
����256ɫλͼ��һ���ֽڸպÿ��Ա�ʾ1�����ء�
�������ɫͼ�������ֽڲ��ܱ�ʾ1������

���ɫͼ�ǲ���Ҫ��ɫ��ģ��ļ�ͷ+��Ϣͷ��ֱ����λͼ���ݣ������в������ɫͼ��
*******************************************************************************************/

void error(char *s)
{
	printf("%s\n",s);
	exit(1);
}

// unsigned long resetbyteorder(unsigned long a)
// {//���ĸ��ֽڵ����ߵ�˳��
// 	unsigned long temp[4];
//     temp[0]=(a&0xff000000)>>24;
//     temp[1]=(a&0x00ff0000)>>8;
//     temp[2]=(a&0x0000ff00)<<8;
//     temp[3]=(a&0x000000ff)<<24;
// 	a=temp[0]+temp[1]+temp[2]+temp[3];
// 	return a;
// }
void makebmpheader(FILE *fp)
{
///BMPλͼ�ļ�ͷ���ܹ�14���ֽ�
	unsigned long i,j;
	unsigned long colorbits, imagebytes;
	unsigned short int type;
	unsigned short int plane,bitcount;
	colorbits=24;//���ɫͼ�������ֽڲ��ܱ�ʾ1������
	linebytes=widthbytes(colorbits*imgwidth);//ÿһ�е��ֽ���������4��������,������ǣ�����Ҫ����
	                                         //imgwidth��JPEG��������
	imagebytes=(unsigned long)imgheight*linebytes;
	type=0x4d42;
     fwrite(&type,sizeof(unsigned short int),1,fp);

//	head.type=(unsigned short int)(((head.type&0xff00)>>8)+((head.type&0x00ff)<<8));
	head.size=imagebytes+0x36;//�ļ�ͷ����Ϣͷ�ܹ�54���ֽڣ�û���õ���ɫ��   
  //  head.size=resetbyteorder(head.size);
	head.reserved=0;
	head.offset=0x36;
  //  head.offset=resetbyteorder(head.offset);
	fwrite(&head,sizeof(head),1,fp);//�ṹheadΪ14���ֽڣ����ļ�ͷheadд��λͼ�ļ�fp��

///BMPλͼ��Ϣͷ
	bmp.size=0x28;//λͼ��ϢͷΪ40���ֽ�
 //   bmp.size=resetbyteorder(bmp.size);
	bmp.width=(unsigned long)imgwidth;
 //   bmp.width=resetbyteorder(bmp.width);
	bmp.height=(unsigned long)imgheight;
  //  bmp.height=resetbyteorder(bmp.height);
   fwrite(&bmp,sizeof(bmp),1,fp);

   plane=1;//������1�����ÿ���
 //  plane=(unsigned short int)(((plane&0xff00)>>8)+((plane&0x00ff)<<8));
   fwrite(&plane,sizeof(unsigned short int),1,fp);
	bitcount=24;
 //  bitcount=(unsigned short int)(((bitcount&0xff00)>>8)+((bitcount&0x00ff)<<8));
   fwrite(&bitcount,sizeof(unsigned short int),1,fp);

	bmp2.compression=0;//��ѹ�����������Compression=BI_RGB�����
	bmp2.imagesize=imagebytes;
  //  bmp2.imagesize=resetbyteorder(bmp2.imagesize);
	bmp2.xpels=0xece;
  //  bmp2.xpels=resetbyteorder(bmp2.xpels);
	bmp2.ypels=0xec4;//�����Զ��壬��ʾÿ�׶��ٸ����ص�
  //  bmp2.ypels=resetbyteorder(bmp2.ypels);
	bmp2.colorused=0;
	bmp2.colorimportant=0;
	fwrite(&bmp2,sizeof(bmp2),1,fp);//�ṹbmpΪ40���ֽڣ����ļ���Ϣͷbmpд��λͼ�ļ�fp��

 	for (i=0;i<imgheight;i++)	 
	  for (j=0;j<linebytes;j++)	  		  
          fputc(0,fp);  //int fputc( int c, FILE *stream ) ��Ȼ��int c��ÿ��ֻдһ���ֽڵ��ļ�fp
	                    //fp--Pointer to FILE structure    	     
}


void initialize(FILE *fp)   //initialize the JPG format file!
{
	unsigned char *p,*q,hfindex,qtindex,number;//numberɨ�����ݶ���ͼ������ĸ���Ns
	int i,j,k, finish=0, huftab1, huftab2, huftabindex, count;
	unsigned short int length=0, flag=0;//Note:"unsigned int", "int" are both 4 bytes(32 bits)!!!!
	                           //only "short int" is 2 bytes, and "char"is 1 bytes.

	fread(&flag,sizeof(short int),1,fp);//Here the result of flag is d8ff but I don't why!
	if (flag!=0xd8ff)//�ж��ļ�ͷ�ǲ���FFD8��ע�����ڴ���FF�ǵ�λ��D8�Ǹ�λ	
		error("Error Jpg File format!");//error() will output the error information and then terminate running.
 
	while (!finish)//ѭ����ȡÿһ����־��
    {
		fread(&flag,sizeof(short int),1,fp);//ÿһ�ζ����fpָ����Զ�����ƶ�
        if (flag!=0xd8ff)
        {       
		fread(&length,sizeof(short int),1,fp); 
		length=((length<<8)|(length>>8));//ע��ʵ�ʶ��������ָߵ�λ����ʾ�Ķ������ļ��ߵ�λ���໥�ߵ���
		} 
		
		//���Ա��뽻���ߵ�λ��lengthΪ��־�εĳ���
		switch(flag)
		{
//////////////////////////////////////////��ʦ������ר��
		case 0xe1ff://///////APP0��
			fseek(fp,length-4,1);break;
        case 0xd8ff:
             break;
////////////////////////////////////
		case 0xe0ff://///////APP0��
			fseek(fp,length-2,1);break;//��ָ���ƶ���APP0��ĩβ
			                          //int fseek( FILE *stream, long offset, int origin )
		//SEEK_SET=0 ��ʾ�ļ��Ŀ�ͷָ��λ��,��SEEK_CUR=1��ʾ��ǰָ��λ�� 




		case 0xdbff://��ɢ����DQT������
			p=(unsigned char *)malloc(length-2);//Allocate the memory space of "length" size.
			                                  //����һ��ָ����ڴ��ָ��p 
			if(p == NULL )
            printf( "Insufficient memory available! The quantization-table may be too large!\n" );
            //Always check the return from malloc, even if the  requested memory  is small.

			fread(p,length-2,1,fp);//������������������浽p�У�ע��p�׵�ַΪ�����ֺ�ĵ�һ���ֽ�PqTq
			qtindex=(*p)&0x0f;//0x0f=00001111�����(*p)ǰ��İ���ֽڣ�Pq��������0��ʾ8bit��1��ʾ16bit��
			//����İ���ֽڣ�Tq���ţ���qtindex����ڼ���������

			q=p+1;//qָ�����������ݿ�ʼ�ĵ�һ���ֽ�
			if (length<68)//ֻ��һ��������
			{
				for (i=0;i<64;i++)
				   Qt[qtindex][i]=(int)*(q++);//��һ���ֽ�ʱ�����ڸߵ�Ϊ�ߵ�������
            }
			else
			{
				for (i=0;i<64;i++)				
				   Qt[qtindex][i]=(int)*(q++);
				qtindex=*(q++)&0x0f;//ȥ���ڶ����PqTq�ֽڵ�ǰ��İ���ֽڣ�Pq�������ȣ���TqΪ��ı��
				for (i=0;i<64;i++)
                   Qt[qtindex][i]=(int)*(q++);														
			}
			free(p);break;


		case 0xc0ff://SOF֡��Ϣ�Σ�C0��ʾBaseline���뷽ʽ
			p=(unsigned char *)malloc(length-2);//Allocate the memory space of "length" size.
			if(p == NULL )
            printf( "Insufficient memory available! The picture may be too large!\n" );
            //Always check the return from malloc, even if the  requested memory  is small.

			fread(p,length-2,1,fp);
			imgheight=((*(p+1))<<8)+(*(p+2));//ͼ��������ء�ע���ڼ���char���������߼������͵�ʽ���char���Զ�ת��Ϊ��������
			imgwidth=((*(p+3))<<8)+(*(p+4));//ͼ���������  ע��ʵ��ͼ������������ǰ�XY����ϵ���ֵģ������������෴
			compressnum=*(p+5);//ͼ������ĸ���
			if ((compressnum!=1)&&(compressnum!=3))			
				error("Error Jpg File Format!");
			if (compressnum==3)
			{
				compressindex[0]=*(p+6);//Y����
				sampleYH=(*(p+7))>>4;//ˮƽ�������ӡ�YH*YV��ָһ��MCU�д������ٸ�Y����8*8�Ŀ飬Ȼ������ٴ�U����
				sampleYV=(*(p+7))&0x0f;//��ֱ��������
				YQt=(int*)Qt[*(p+8)];//ʹ�õ���������   C1,H1V1,Tq1

				compressindex[1]=*(p+9);//U����
				sampleUH=(*(p+10))>>4;
				sampleUV=(*(p+10))&0x0f;
				UQt=(int*)Qt[*(p+11)];//C2,H2V2,Tq2

				compressindex[2]=*(p+12);//V����
				sampleVH=(*(p+13))>>4;
				sampleVV=(*(p+13))&0x0f;
				VQt=(int*)Qt[*(p+14)];//C3,H3V3,Tq3
			}
			else//ֻ��һ�������Ҷ�ͼ��Ĭ����ͬһ������������Ϊ1*1����������
			{
				compressindex[0]=*(p+6);
				sampleYH=(*(p+7))>>4;
				sampleYV=(*(p+7))&0x0f;
				YQt=(int*)Qt[*(p+8)];

				compressindex[1]=*(p+6);
				sampleUH=1;
				sampleUV=1;
				VQt=(int*)Qt[*(p+8)];

				compressindex[2]=*(p+6);
				sampleVH=1;
				sampleVV=1;
				VQt=(int*)Qt[*(p+8)];
			}
			free(p);break;


		case 0xc4ff:			
			p=(unsigned char *)malloc(length-2);//��Ϊ��������һ���ֽ�0xff�������ж�ѭ����ʱ����		    
			if(p == NULL )
            printf( "Insufficient memory available! The picture may be too large!\n" );
            //Always check the return from malloc, even if the  requested memory  is small.

			fread(p,length-2,1,fp);
		//	p[length-1]=0xff;//��Ϊ��������һ���ֽ�0xff�������ж�ѭ����ʱ����
		//	if (length<0xd0)//������������ж�ֻ��һ�����д��Ľ���0xd0=208 һ��huffman��������ж��ٸ��ֽ�
		//	{
				huftab1=(int)(*p)>>4;
				huftab2=(int)(*p)&0x0f;
				huftabindex=huftab1*2+huftab2;//ֱ�ӽ�Tc|Th���ɱ�ı�ţ�huftabindex=��2*Tc+Th��
				q=p+1;count=0;//count�����һ��huf������ֽ���
				for (i=0;i<16;i++)
				{

                   codelen[huftabindex][i]=(int)(*(q++));//codelen��ʾÿ������i+1�����Ӧ�ĸ���
				   count+=codelen[huftabindex][i];//codevalue���ֵ��ֽ���
				} 
				j=0;count+=17;//��ʱcount��ʾ��һ������ֽ���
				for (i=0;i<16;i++)					    					
				    if (codelen[huftabindex][i]!=0)	//���ĳ������(i+1)����ĸ�����Ϊ��				
						{
							k=0;
					        while (k<codelen[huftabindex][i])
							{
					         	codevalue[huftabindex][k+j]=(int)(*(q++));//�Ѻ���value�����������ζ�Ӧ��ֵ��ȡ����
					        	k++;//codevalue[4][j]=(Z,R)���������к�
							}
					      j+=k;
						}
			
				i=0;
				while (codelen[huftabindex][i]==0) i++;//�ӵ�һ����ĸ�����Ϊ��ĳ��ȿ�ʼ
				for (j=0;j<i;j++)
					{
						hufmin[huftabindex][j]=0;//j���ȵ���Ŀ�ʼ�루������intֵ��ʾ�ģ�
						hufmax[huftabindex][j]=0;//j���ȵ���Ľ����루������intֵ��ʾ�ģ�
					}
				hufmin[huftabindex][i]=0;//��һ�������ʼֵ���涨Ϊ0��int�͵�ֵ��
				hufmax[huftabindex][i]=codelen[huftabindex][i]-1;
				for (j=i+1;j<16;j++)
				{	
					if (codelen[huftabindex][j-1]!=0)
					{								
					    hufmin[huftabindex][j]=(hufmax[huftabindex][j-1]+1)<<1;//����һλ��j+1���ȵ���Ŀ�ʼ��                       				        
						if (codelen[huftabindex][j]!=0)										    
					    	hufmax[huftabindex][j]=hufmin[huftabindex][j]+codelen[huftabindex][j]-1; //j+1���ȵ���Ľ�����
						else//���j+1���ȵ������Ϊ�����������ֵ����Сֵ��ͬ����Ȼ�������뵫�����õ���ֻ��Ϊ���νӺ����������
							hufmax[huftabindex][j]=hufmin[huftabindex][j];
					}


                    else //���ǰ�������Ϊ�㣬�����������ʱֻ��λ����1
					{								
					    hufmin[huftabindex][j]=(hufmax[huftabindex][j-1])<<1;//ֻ��λ����1��j+1���ȵ���Ŀ�ʼ��
				    	if (codelen[huftabindex][j]!=0)										    
					    	hufmax[huftabindex][j]=hufmin[huftabindex][j]+codelen[huftabindex][j]-1; //j+1���ȵ���Ľ�����
						else//���j+1���ȵ������Ϊ�����������ֵ����Сֵ��ͬ����Ȼ�������뵫�����õ���ֻ��Ϊ���νӺ����������
							hufmax[huftabindex][j]=hufmin[huftabindex][j];
					}		

				}  
				codepos[huftabindex][0]=0;//����Ϊj+1�ĵ�һ��������Ӧ��codevalue[]������
				for (j=1;j<16;j++)
					codepos[huftabindex][j]=codelen[huftabindex][j-1]+codepos[huftabindex][j-1];
		  //}

             tempp=count; 
		   //	else//FFC4���ж��huf��
		//	if(count<length-2)//FFC4���ж��huf��
            while (tempp<length-2)
			{
				
               // unsigned char *tempp;
                //tempp=p;
			//	tempp+=count;//��ָ���Ƶ��ڶ�����Ŀ�ʼ��
				p+=count;
				hfindex=*p;
			//	while (hfindex!=0xff)//��Ϊ��������һ���ֽ�0xff�������жϱ��ʱ����
				    
						huftab1=(int)hfindex>>4;
						huftab2=(int)hfindex&0x0f;
						huftabindex=huftab1*2+huftab2;
						q=p+1;count=0;//count��ʾ��һ��huf������ֽ������������ۼӵõ�
						for (i=0;i<16;i++)
							{
								codelen[huftabindex][i]=(int)(*(q++));
								count+=codelen[huftabindex][i];//codevalue���ֵ��ֽ���
							}
						count+=17;j=0;
						for (i=0;i<16;i++)	//����ͬ�϶����ڶ���huf���							
							if (codelen[huftabindex][i]!=0)
								{
									k=0;
									while (k<codelen[huftabindex][i])
									{
										codevalue[huftabindex][k+j]=(int)(*(q++));
									    k++;
									}
									j+=k;
								}
                        i=0;
						while (codelen[huftabindex][i]==0) i++;
                        for (j=0;j<i;j++)
                           {
							   hufmin[huftabindex][j]=0;
							   hufmax[huftabindex][j]=0;
                            }
						hufmin[huftabindex][i]=0;
						hufmax[huftabindex][i]=codelen[huftabindex][i]-1;
						for (j=i+1;j<16;j++)
							{
							    if (codelen[huftabindex][j-1]!=0)
								{								
					                hufmin[huftabindex][j]=(hufmax[huftabindex][j-1]+1)<<1;//����һλ��j+1���ȵ���Ŀ�ʼ��                       				        
						            if (codelen[huftabindex][j]!=0)										    
					                 	hufmax[huftabindex][j]=hufmin[huftabindex][j]+codelen[huftabindex][j]-1; //j+1���ȵ���Ľ�����
					               	else//���j+1���ȵ������Ϊ�����������ֵ����Сֵ��ͬ����Ȼ�������뵫�����õ���ֻ��Ϊ���νӺ����������
						            	hufmax[huftabindex][j]=hufmin[huftabindex][j];
								}

                                else //���ǰ�������Ϊ�㣬�����������ʱֻ��λ����1
								{								
					                 hufmin[huftabindex][j]=(hufmax[huftabindex][j-1])<<1;//ֻ��λ����1��j+1���ȵ���Ŀ�ʼ��
				    	             if (codelen[huftabindex][j]!=0)										    
					                 	hufmax[huftabindex][j]=hufmin[huftabindex][j]+codelen[huftabindex][j]-1; //j+1���ȵ���Ľ�����
					             	 else//���j+1���ȵ������Ϊ�����������ֵ����Сֵ��ͬ����Ȼ�������뵫�����õ���ֻ��Ϊ���νӺ����������
							            hufmax[huftabindex][j]=hufmin[huftabindex][j];
								}			
							}
				    	codepos[huftabindex][0]=0;
						for (j=1;j<16;j++)
							codepos[huftabindex][j]=codelen[huftabindex][j-1]+codepos[huftabindex][j-1];
					//	p+=count;
					//	hfindex=*p;//ȡ���������Tc|Th��ѭ������Ĺ��� 	
						tempp+=count;								            
			}
			p-=(tempp-count);
			free(p);//ѭ��������ָ���λ��ʼ�㣬�ͷ�����buffer
			break;

		case 0xddff://DRI�Σ��������ü�����ô�СRi����ÿ��scan����Ri��MCU
			p=(unsigned char *)malloc(length-2);
			if(p == NULL )
            printf( "Insufficient memory available! The picture may be too large!\n" );
            //Always check the return from malloc, even if the  requested memory  is small.
			fread(p,length-2,1,fp);
			restart=((*p)<<8)|(*(p+1));//restart=Ri��DRI���е���������ֽ�Ri�������ֽڱ�ʾһ��SCAN��ÿ��
		            //MCU-Segment���������MCU�ĸ���������segment֮����RST��־�֣�RST=0����0��7ѭ����
		        	//interval��ʾÿ��segment��ѭ�����˵ڼ���MCU��interval=0-Ri��
			free(p);break;

		case 0xdaff://SOS�Σ�start of scan���������ͼ������
			p=(unsigned char *)malloc(length*sizeof(unsigned char)-2);
            fread(p,length-2,1,fp);
			number=*p;//ɨ�����ݶ���ͼ������ĸ���Ns
			if (number!=compressnum)
			error("Error Jpg File Format!");
			q=p+1;
			for (i=0;i<compressnum;i++)//��ʾͼ������ĸ���
			{
				if (*q==compressindex[0])//����ͼ������compressindex��ʾ�ڼ���ͼ��ı��
				{
					YDCindex=(*(q+1))>>4;//hufman_DC��ı�ţ���Ϊ0��1
					YACindex=(*(q+1)&0x0f)+2;//hufman_AC��ı��,��Ϊ2��3���ǰ�0123����ŵ�
				}
				else//����ɫ��ͼ�����õı���һ����
				{
					UVDCindex=(*(q+1))>>4;
					UVACindex=(*(q+1)&0x0f)+2;
				}
				q+=2;
			}//SOS�κ��滹��Ss,Se,Ah|Al,��Baseline��ʽ�޹أ��˴�û�д���
			finish=1;free(p);break;

		case 0xd9ff://�ļ������α�־
			error("Error Jpg File Format!");
			break;

		default://������(FFD?��flag=D?FF)Ϊ��־�Ķδ˴���û�п���
			if ((flag&0xf000)!=0xd000)			
				fseek(fp,length-2,SEEK_CUR);//ֱ������
			break;			
		}
    }   	
}


void savebmp(FILE *fp)//�˴�ֻ����һ��MCU��ͼ�����������ﻹ��ѭ��
{
  int i,j;
  unsigned char r,g,b;
  long y,u,v,rr,gg,bb;
  for (i=0;i<sampleYV*8;i++)//i��ʾ��
  {
	  if ((height+i)<imgheight)
	  {//height��BMP��ͼ��ĸߣ�imgheight��JPEG�ĸߣ����ص㣩
		  fseek(fp,(unsigned long)(imgheight-height-i-1)*linebytes+3*width+54,0);//��ʼheight=0��width=0�Ƶ����ļ������һ�п�ʼ��
                  //3*widthÿ����������3���ֽ����洢�ģ�Width��ʾÿһ�е����أ����һ��MCUʱWidthʼ��Ϊ0���ڶ���ʱΪ1�������ִ����һ�п�ʼ��
                  //������0��ʾָ����ļ�����ʼλ�ÿ�ʼ��
//һ����˵��.bMP�ļ������ݴ��µ��ϣ������ҵġ�Ҳ����˵�����ļ������ȶ�������ͼ��������һ�е�
//��ߵ�һ�����أ�Ȼ������ߵڶ������ء����������ǵ����ڶ�����ߵ�һ�����أ���ߵڶ������ء���
//�������� �����õ�����������һ�е�����һ�����ء�
		  for (j=0;j<sampleYH*8;j++)//j��ʾ��
		  {
			  if ((width+j)<imgwidth)
			  {
				  y=Y[i*8*sampleYH+j];//��һ��MCU��ĵ�i�е�ÿ�����������i����MCU�У�j����MCU��
				  u=U[(i/VYtoU)*8*sampleYH+j/HYtoU];//û�в�������/���õ�������һ��/����ͬ��ֵ������0
				  v=V[(i/VYtoV)*8*sampleYH+j/HYtoV];

				  rr=((y<<8)+359*v)>>8;//��YUVת��ΪRGB���˴��漰��С�����ɶ������������⣬�д��о�
				  gg=((y<<8)-88*u-183*v)>>8;
				  bb=((y<<8)+301*u)>>8;

				 
								 
				  //if (rr&0xffffff00)//У��rr����255��Ϊ���������
				    if (rr>255)r=255;else if (rr<0)r=0;else  r=(unsigned char)rr;
				 // if (gg&0xffffff00)
				    if (gg>255)g=255;else if (gg<0)g=0;else g=(unsigned char)gg;
				 // if (bb&0xffffff00)
				    if (bb>255)b=255;else if (bb<0)b=0;else	 b=(unsigned char)bb;

				fputc(b,fp);fputc(g,fp);fputc(r,fp);//�ֱ��bgr����������ֽڵĸߡ��С���byte														
			  }
			  else break;
		  }
	  }
	  else break;
  }
}


unsigned char readbyte(FILE *fp)
{
  unsigned char c;
  c=fgetc(fp);

  if (c==0xff)
    fgetc(fp);//����֡ͷFFXX�ȣ���������XX����ȥ����C���ص���Ȼ��FF

  bitpos=8;curbyte=c;
  return c; 
}

int DecodeElement(FILE *fp)//fp�Ѿ�ָ������Ҫ���������
{///////////////////////////////��һ�������
	unsigned int codelength;//huf��ĳ��ȣ�codelength-1Ϊ�ó��ȵ����������е�����ֵ
	unsigned int thiscode,tempcode;
	unsigned short int temp, neww;
	unsigned char hufbyte,runsize,tempsize, sign;
	unsigned char newbyte,lastbyte;
	if (bitpos>=1)//������벻��block�ĵ�һ���룿��
	{
		bitpos--;
		thiscode=(unsigned char)curbyte>>bitpos;
		curbyte=curbyte&And[bitpos];
	}
	else//�������Ϊһ��block�ĵ�һ���롣bitpos��curbyte��ʼֵΪ0
	{ 
		lastbyte=readbyte(fp);
		bitpos--;
		newbyte=curbyte&And[bitpos];//��ʾȡ�����λ1��һλ����3����λ����7����λ����15����λ��
		thiscode=lastbyte>>7;//thiscodeȡ�������ֽڵĵ�1λ
		curbyte=newbyte;//������7λ
	}

	codelength=1;
	while((thiscode<hufmin[HufTabindex][codelength-1])||(codelen[HufTabindex][codelength-1]==0)||(thiscode>hufmax[HufTabindex][codelength-1]))
	{//thiscode��huf����û�������������ִ��
		if(bitpos>=1)
		{
			bitpos--;
			tempcode=(unsigned char)curbyte>>bitpos;//ȡ��2λ
			curbyte=curbyte&And[bitpos];//������6λ
		}
		else
		{
			lastbyte=readbyte(fp);
			bitpos--;
			newbyte=curbyte&And[bitpos];//newbyteȡ�������ֽڵĺ���λ
			tempcode=(unsigned char)lastbyte>>7;//tempcodeȡ�������ֽڵ�ǰһλ
			curbyte=newbyte;
		}
		thiscode=(thiscode<<1)+tempcode;//thiscode=��ȡ�ĵ�һλ��ȡ�ĵڶ�λ�����һ��
		codelength++;
		if (codelength>16)
			error("Error Jpg File Format!");		
	}

	temp=thiscode-hufmin[HufTabindex][codelength-1]+codepos[HufTabindex][codelength-1];
	//temp��ʾ��ǰ�������thiscode���ڵ��ж�Ӧ������codevalue[4][256]�����ţ���������кŲ�һ����Ӧ
	//codepos[HufTabindex][codelength-1]��ʾ����Ϊcodelength�ĵ�һ�������ڵ���(����Ӧ��codevalue��ֵ����ֵ��0��ʼ)
	//codelen��ʾÿ�����ȵ����Ӧ�ĸ�����
     hufbyte=(unsigned char)codevalue[HufTabindex][temp];//hufbyte��ʾ�����У������=(Z,R)���������к�
	 run=(int)(hufbyte>>4);//ȡ�кŵĸ�4λ,��ʾ����ĸ���Z��(Z,R)|C
	 runsize=hufbyte&0x0f;//ȡ�кŵĵ�4λ�����ܾ��Ǳ�ʾ�к�
	 if (runsize==0)//0�ж�Ӧ��valueֻ����0
	 {
		 value=0;//value��ʾ�����������ֵ
		 return 1;
	 }
     tempsize=runsize;//runsizeȡ�кŵĵ�4λ����ʾ�к�1��16
	 if (bitpos>=runsize)//��������һ���ֽڻ�ʣbitposλ���жϹ�������������runsizeλ
	 {
		 bitpos-=runsize;//bitpos��������runsizeλ����������������Ϊ(R,Z)|C���к�C��λ��������R����ͬ��
		 neww=(unsigned char)curbyte>>bitpos;//neww��Ϊ�к�C���������
		 curbyte=curbyte&And[bitpos];//����ʣ�µ���λ
	 }
	 else
	 {
		 neww=(unsigned short int)curbyte;
		 tempsize-=bitpos;
         while (tempsize>8)
         {
			 lastbyte=readbyte(fp);//�ٶ�һ���ֽڳ���
			 neww=(neww<<8)+(unsigned char)lastbyte;
			 tempsize-=8;
         }
		 lastbyte=readbyte(fp);
		 bitpos-=tempsize;
		 neww=(neww<<tempsize)+(lastbyte>>bitpos);
		 curbyte=lastbyte&And[bitpos];
	 }
	 sign=neww>>(runsize-1);//ȡneww�ĵ�һλ��runsize��ʾ�кŵĵ�4λ,���ܾ��Ǳ�ʾ�к�
	 if (sign)//�����Ϊ������ֱ�Ӹ�ֵ��sign�ж���������Ϊ�������кŵ�һλ�϶���1��������֤
	 value=neww;//value��ʾÿ����������ֵ
	 else
	 {
        neww=neww^0xffff;//��򣬵���ȡ������Ϊͬһ������������Ӧ���к�ǡ�õ��ڻ���ȡ��
		temp=0xffff<<runsize;
		value=-(int)(neww^temp);//�Ѹ�λȡ�����ɵ�1��Ϊ0��value��ʾÿ����������ֵ
	 }
	 return 1;	 
}


int HufBlock(FILE *fp,unsigned char dchufindex,unsigned char achufindex)	
{////���ݲ�ͬ��DC��AC������fp��ǰ��ָ��block����뵽
 //blockbuffer[64]�д�������fpҲ��Ӧ������ƶ�һ����ָ����һ����
    int i,count=0;
	HufTabindex=dchufindex;//ֱ���������ֵ����HufTabindex
	if (DecodeElement(fp)!=1)//��ֱ�����һ��ֱ�������
	return 0;
	blockbuffer[count++]=value;//blockbuffer[64]����һ����,��value����blockbuffer[0]
	//value��ʾÿ����������ֵ������ǵ�һ�������ʾֱ��������ֺ��ֵ��
	//��DecodeMCUBlock������Ҫ��Ӳ��ܵõ�������ֱ��ϵ��
	HufTabindex=achufindex;//�����������ֵ����HufTabindex
	while(count<64)//���Block�еڶ��������һ��ֵ
	{              //ѭ����һ��block�е�63���������ݽ����
		if (DecodeElement(fp)!=1)
		return 0;
		if ((run==0)&&(value==0))//����ϵ����Ϊ�㡣run��ʾ����ĸ���
		{
			for (i=count;i<64;i++)
			blockbuffer[i]=0;
			count=64;			
		}
		else
		{
			for (i=0;i<run;i++)//��ʾÿ������ϵ��֮ǰ��0�ĸ���
			blockbuffer[count++]=0;
			blockbuffer[count++]=value;			
		}		
	}
	return 1;
}

int DecodeMCUBlock(FILE *fp)//fp1�Ѿ��Ƶ���MCU�鴦����һ��MCU��������ȫ���������
{
	int i,j,*pMCUBuffer;
	if (intervalflag)//��ʾscan��һ��segment��������һ��segment��ʼǰ��һЩ��ʼ����ʼ��
	{
		fseek(fp,2,1);//��SEEK_CUR=1��ʾ��ǰָ��λ�ã���ʾ�����ڶ���segment��ʼǰ��RST��0-7ѭ������ʶ�����ֽ�
//int fseek( FILE *stream, long offset, int origin );
//If successful, fseek returns 0. Otherwise, it returns a nonzero value
		ycoef=ucoef=vcoef=0;//��һ��û�в�ֵ�ֱ��������ϵ������һ��segment����ֱ�����в�֣��ڶ�segment���������½��в�֣�����������
//?????????????????????????????????????????????????????????????????����ͨ��������ȷ�ϣ�������һ��ע�͵�	
		bitpos=0;curbyte=0;
	}
	
	switch(compressnum)
	{
     	case 3://��ɫͼ��
			pMCUBuffer=MCUbuffer;//MCUbuffer[10*64]һ��MCU�����ֻ����10��8*8�飬ע��ֻ�Ǹ�һά����
			for (i=0;i<sampleYH*sampleYV;i++)//��һ��MCU�е�Y������sampleYH*sampleYV�������
			{
				if (HufBlock(fp,YDCindex,YACindex)!=1)//���ݲ�ͬ��DC��AC������fp��ǰ��ָ��block����뵽
					//blockbuffer[64]�д�������fpҲ��Ӧ������ƶ�һ����ָ����һ����
				return 0;
				blockbuffer[0]=blockbuffer[0]+ycoef;//blockbuffer[0]��ʼֵ��HufBlock�������value
				ycoef=blockbuffer[0];//ycoef��ÿ����ĵ�һ��������ʾÿ�����ֱ��������ֱ������
				//�ǲ�ֱ��룬����Ҫ��Ӳ��ܵõ���һ��ֱ������
				for (j=0;j<64;j++)
				*pMCUBuffer++=blockbuffer[j];//��MCU�еĵ�j��block����ָ�룬ע��pMCUBuffer[64*10]ֻ�Ǹ�һά����				
			//һ��MCU�е�����Ԫ�ض�˳�������һά����pMCUBuffer��
			}
			for (i=0;i<sampleUH*sampleUV;i++)
			{
				if (HufBlock(fp,UVDCindex,UVACindex)!=1)//U��V��������һ���Ľ�����ֱ����
				return 0;
				blockbuffer[0]=blockbuffer[0]+ucoef;
				ucoef=blockbuffer[0];
				for (j=0;j<64;j++)				
					*pMCUBuffer++=blockbuffer[j];								
			}

			for (i=0;i<sampleVH*sampleVV;i++)
			{
				if (HufBlock(fp,UVDCindex,UVACindex)!=1)
				return 0;
				blockbuffer[0]=blockbuffer[0]+vcoef;
				vcoef=blockbuffer[0];
				for (j=0;j<64;j++)				
					*pMCUBuffer++=blockbuffer[j];								
			}
			break;

		case 1://�ڰ�ͼ��
			pMCUBuffer=MCUbuffer;//���漰���������ӣ�һ��Y��������൱��һ��MCU
			if (HufBlock(fp,YDCindex,YACindex)!=1)
			return 0;
			blockbuffer[0]=blockbuffer[0]+ycoef;
			ycoef=blockbuffer[0];
			for (j=0;j<64;j++)				
			*pMCUBuffer++=blockbuffer[j];								
			for (i=0;i<128;i++)
			*pMCUBuffer++=0;//Ҳ�ǰ�Y��U��V�������洢��ֻ�����������������������0			
			break;
			
		default:
			error("Error Jpg File Format!");
	}
	return 1;
}



void idct(long *p,int k)
{
   long x,x0,x1,x2,x3,x4,x5,x6,x7;
   x1=p[k*4]<<11;
   x2=p[k*6];
   x3=p[k*2];
   x4=p[k*1];
   x5=p[k*7];
   x6=p[k*5];
   x7=p[k*3];
   x0=(p[0]<<11)+1024;
   x=565*(x4+x5);x4=x+2276*x4;x5=x-3406*x5;
   x=2408*(x6+x7);x6=x-799*x6;x7=x-4017*x7;
   x=1108*(x3+x2);x2=x-3784*x2;x3=x+1568*x3;

   x=x6;x6=x5+x7;x5-=x7;x7=x0+x1;x0-=x1;x1=x+x4;x4-=x;
   x=x5;x5=x7-x3;x7+=x3;x3=x0+x2;x0-=x2;x2=(181*(x4+x)+128)>>8;x4=(181*(x4-x)+128)>>8;
   p[0]=(x7+x1)>>11;
   p[k*1]=(x3+x2)>>11;  
   p[k*2]=(x0+x4)>>11;  p[k*3]=(x5+x6)>>11;   	   
   p[k*4]=(x5-x6)>>11;  p[k*5]=(x0-x4)>>11;
   p[k*6]=(x3-x2)>>11; p[k*7]=(x7-x1)>>11;
}

void IDCTint(long *metrix)
{
	int i;
	for (i=0;i<8;i++)
		idct(metrix+8*i,1);
	for (i=0;i<8;i++)
         idct(metrix+i,8);  
}

void IQtZBlock(int *s,long*d,int *pQt,int correct)
{
	int i,j,tag;
	long *pbuffer,buffer[8][8];
	for (i=0;i<8;i++)
	  for (j=0;j<8;j++)
	  {
		  tag=Z[i][j];         //Z[i][j]�洢����zig-zag���е�˳������
		  buffer[i][j]=(long)s[tag]*(long)pQt[tag];//ע��buffer�����˳���Ѿ��任��ԭ���ÿ��ÿ�е�����������
	  }
	pbuffer=(long *)buffer;
	IDCTint(pbuffer);//����ɢ���ұ任
	for (i=0;i<8;i++)
	  for (j=0;j<8;j++)
	    d[i*8+j]=(buffer[i][j]>>3)+correct;//����������������������?????>>3
}

void IQtZMCU(int xx, int yy,int offset,int *pQt,int correct)
{
	int i,j,*pMCUBuffer;//������֮ǰ��buffer
	long *pQtZMCUBuffer;//������֮���buffer
    pMCUBuffer=MCUbuffer+offset;//offset��ʾһ��MCU��Y��U��V����������ʼλ��
    pQtZMCUBuffer=QtZMCUbuffer+offset;
	for(i=0;i<yy;i++)//��ֱ������
       for(j=0;j<xx;j++)//ˮƽ������
          IQtZBlock(pMCUBuffer+(i*xx+j)*64,pQtZMCUBuffer+(i*xx+j)*64,pQt,correct);
}

void getYUV(int xx, int yy, long *buf,int offset)
{//	getYUV(sampleYH,sampleYV,Y,Yinbuf)
 //Yinbuf��ʾ��MCU��Y��������ʼλ��
	 int i,j,k,n;
	 long *pQtZMCU;
	 pQtZMCU=QtZMCUbuffer+offset;
	 for(i=0;i<yy;i++)//��ֱ����sampleYV
		 for(j=0;j<xx;j++)//ˮƽ����sampleYH��
			 for(k=0;k<8;k++)//��
				 for(n=0;n<8;n++)//��
					 buf[(i*8+k)*sampleYH*8+j*8+n]=*pQtZMCU++;//��������ȷ����MCU�еĲ�ͬ����������ͬ��buf����ȥ
            //ע��pQtZMCU�����˳���Ѿ���IQtZBlock�����б任��ԭ���ÿ��ÿ�е�����������
}

void decode(FILE *fp1,FILE *fp2)
{
	int Yinbuf,Uinbuf,Vinbuf;
	YinMCU=sampleYH*sampleYV;//sampleXX ��block��Ŀ
	UinMCU=sampleUH*sampleUV;
	VinMCU=sampleVH*sampleVV;

	HYtoU=sampleYH/sampleUH;//HYtoU����һ��MCU�д�ֱ��������YBlock��Ŀ��UBlock��Ŀ�ı�ֵ
	VYtoU=sampleYV/sampleUV;
    HYtoV=sampleYH/sampleVH;
	VYtoV=sampleYV/sampleVV;

	Yinbuf=0;//��MCU��Y��������ʼλ��
	Uinbuf=YinMCU*64;//��MCU��U��������ʼλ��
	Vinbuf=(YinMCU+UinMCU)*64;//��MCU��V��������ʼλ��

	while (DecodeMCUBlock(fp1))//fp1�Ѿ��Ƶ���MCU�鴦��ѭ������ÿ��MCU��
	{                         //��ֻ��Y����ʱ���ڰ�ͼ�񣩣�һ��block����൱��һ��MCU
		interval++;
		if ((restart)&&(interval%restart==0))//restart=Ri��DRI���е���������ֽڣ������ֽڱ�ʾһ��SCAN��ÿ��
	//segment���������MCU�ĸ�����MCU�Ǵ�1��ʼ��MCU1������segment֮����RST��־�֣��ñ�־�ִ�0��7ѭ��
    //restart=0��ʾ��ʹ�ü�����÷�ʽ�������ݣ�ͬʱsegment֮��Ҳû��RST��־�֣���SCAN�����е�MCU��������
	//interval��ʾÿ��segment��ѭ�����˵ڼ���MCU��interval=1-Ri��
			intervalflag=1;//intervalflag=1��ʾscan��һ��segment��������һ��segment��ʼ�ı�ʶ������0��ʾ��û����
		else
			intervalflag=0;

		IQtZMCU(sampleYH,sampleYV,Yinbuf,YQt,128);//�������ͷ���ɢ���ұ任
		IQtZMCU(sampleUH,sampleUV,Uinbuf,UQt,0);//��ɢ���ұ任ֻ����-128��127��ֵ���任֮ǰ����ȥ��128
		IQtZMCU(sampleVH,sampleVV,Vinbuf,VQt,0);//Ϊʲôֻ��Y����Ҫ��128�أ������������ȴ���֤
		
		getYUV(sampleYH,sampleYV,Y,Yinbuf);//���������YUV����
		getYUV(sampleUH,sampleUV,U,Uinbuf);
		getYUV(sampleVH,sampleVV,V,Vinbuf);
		savebmp(fp2);//�˴�ֻ����һ��MCU��ͼ��
		width+=sampleYH*8;
		if (width>=imgwidth)
		{
			width=0;
			height+=sampleYV*8;
		}
		if ((width==0)&&(height>=imgheight))
		break;		
	}
}


void main()
{
   FILE *fp1,*fp2;
   if ((fp1=fopen("flower.jpg","rb"))==NULL)
	   error("Can not open Jpg File!");
   if ((fp2=fopen("flower.bmp","wb"))==NULL)
       error("Can not create Bmp File!");
   initialize(fp1);
   makebmpheader(fp2);
   decode(fp1,fp2);

   fclose(fp1);fclose(fp2);  
}